/* SPDX-License-Identifier: GPL-2.0-or-later */
/*
 * baseline sepolicy 接管：init 首次加载策略时拍快照，app uid 的 selinuxfs
 * 探测都用快照应答，root 在运行时注入的 type / rule 对 app 不可见。
 */

#include "selinux_hide.h"

#include <baselib.h>
#include <common.h>
#include <hook.h>
#include <kallsyms.h>
#include <ksyms.h>
#include <kputils.h>
#include <log.h>
#include <linux/security/selinux/include/security.h>
#include <linux/security.h>
#include <uapi/asm-generic/errno.h>
#include <linux/fs.h>
#include <linux/kernel.h>
#include <linux/vmalloc.h>
#include <barrier.h>
#include <asm/atomic.h>

#define APP_UID_MIN              10000

#define POLICY_MAGIC             0xf97cff8c
#define POLICY_MAGIC_STR         "SE Linux"
#define POLICY_MIN_LEN           64u
#define POLICY_MAX_LEN           (32u * 1024u * 1024u)

#define NAME_MAX_LEN             255u
#define VALUE_MAX                65536u

#define TYPEDATUM_PRIMARY        0x1u
#define TYPEDATUM_ATTRIBUTE      0x2u
#define TYPEDATUM_ALIAS          0x4u

/* baseline 中 type 多达数千；其他三表通常几十到几百，分两档容量 */
#define NTAB_BIG_ENTRIES         32768u
#define NTAB_BIG_NAMES_MAX       (4u * 1024u * 1024u)
#define NTAB_SMALL_ENTRIES       2048u
#define NTAB_SMALL_NAMES_MAX     (128u * 1024u)

#define SYM_NUM_MAX              16u   /* 上游恒为 8，留余量挡 OEM 异常 */

enum {
    SYM_COMMONS = 0,
    SYM_CLASSES = 1,
    SYM_ROLES   = 2,
    SYM_TYPES   = 3,
    SYM_USERS   = 4,
    SYM_BOOLS   = 5,
    SYM_LEVELS  = 6,
    SYM_CATS    = 7,
};

#define V_POLCAP                 22
#define V_PERMISSIVE             23
#define V_BOUNDARY               24
#define V_NEW_OBJECT_DEFAULTS    27
#define V_DEFAULT_TYPE           28
#define V_CONSTRAINT_NAMES       29

#define CEXPR_NAMES              5

typedef ssize_t (*write_op_fn)(struct file *, char *, size_t);

struct nament {
    u32 off;
    u16 len;
    u16 _pad;
};

struct nametab {
    struct nament *ents;
    char          *pool;
    u32 count;
    u32 cap;
    size_t pool_len;
    size_t pool_cap;
};

static struct {
    bool installed;
    bool captured;          /* smp_store_release published */
    atomic_t capturing;     /* once guard for capture_baseline */

    void *orig_context_write;
    void *orig_access_write;
    void *orig_setprocattr;
    void *orig_load_policy;
    void *orig_read_policy;

    void   *policy_raw;
    size_t  policy_len;
    u32     policy_vers;

    struct nametab types;
    struct nametab users;
    struct nametab roles;
    struct nametab classes;
} state;

static inline u32 read_le32(const void *p)
{
    const u8 *b = p;
    return (u32)b[0] | ((u32)b[1] << 8) | ((u32)b[2] << 16) | ((u32)b[3] << 24);
}

static inline bool is_space(char c)
{
    return c == ' ' || c == '\t' || c == '\n' || c == '\r';
}

static inline bool is_name_char(char c)
{
    return (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') ||
           (c >= '0' && c <= '9') || c == '_' || c == '.' || c == '-';
}

static size_t trim_tail(const char *s, size_t len)
{
    while (len && (is_space(s[len - 1]) || s[len - 1] == '\0'))
        len--;
    return len;
}

/* "user:role:type[:level]" → user/role/type 三段；level 可缺 */
static int extract_tuple(const char *ctx, size_t len,
                         const char **u, size_t *u_len,
                         const char **r, size_t *r_len,
                         const char **t, size_t *t_len)
{
    const char *p, *end, *start;

    if (!ctx || !u || !r || !t || !len)
        return -EINVAL;
    len = trim_tail(ctx, len);
    if (!len)
        return -EINVAL;

    p = ctx;
    end = ctx + len;

    start = p;
    while (p < end && *p != ':') p++;
    if (p == start || p == end) return -EINVAL;
    *u = start; *u_len = p - start; p++;

    start = p;
    while (p < end && *p != ':') p++;
    if (p == start || p == end) return -EINVAL;
    *r = start; *r_len = p - start; p++;

    start = p;
    while (p < end && *p != ':') p++;
    if (p == start) return -EINVAL;
    *t = start; *t_len = p - start;
    return 0;
}

static int next_token(const char **cur, const char *end,
                      const char **tok, size_t *tok_len)
{
    const char *p = *cur;

    while (p < end && is_space(*p)) p++;
    if (p >= end || *p == '\0') return -EINVAL;

    *tok = p;
    *tok_len = 0;
    while (p < end && !is_space(*p) && *p != '\0') {
        p++;
        (*tok_len)++;
    }
    *cur = p;
    return 0;
}

/* ===== nametab ===== */

static bool ntab_has(const struct nametab *t, const char *name, size_t len)
{
    u32 i;
    for (i = 0; i < t->count; i++) {
        const struct nament *e = &t->ents[i];
        if (e->len == len && !lib_memcmp(t->pool + e->off, name, len))
            return true;
    }
    return false;
}

static int ntab_add(struct nametab *t, const char *name, u32 len)
{
    struct nament *e;

    if (ntab_has(t, name, len))
        return 0;
    if (t->count >= t->cap || t->pool_len + len > t->pool_cap)
        return -ENOMEM;

    e = &t->ents[t->count];
    e->off = (u32)t->pool_len;
    e->len = (u16)len;
    lib_memcpy(t->pool + t->pool_len, name, len);
    t->count++;
    t->pool_len += len;
    return 0;
}

static void ntab_free(struct nametab *t)
{
    if (!t) return;
    if (t->ents) vfree(t->ents);
    if (t->pool) vfree(t->pool);
    lib_memset(t, 0, sizeof(*t));
}

static int ntab_alloc(struct nametab *t, u32 ents_cap, size_t pool_cap)
{
    lib_memset(t, 0, sizeof(*t));
    t->ents = vmalloc(sizeof(struct nament) * ents_cap);
    t->pool = vmalloc(pool_cap);
    if (!t->ents || !t->pool) {
        ntab_free(t);
        return -ENOMEM;
    }
    t->cap = ents_cap;
    t->pool_cap = pool_cap;
    return 0;
}

/* ===== policydb 二进制游标 =====
 * 按 selinux/ss/policydb.c::policydb_write 的字节流逐字段读，跨 4.9~6.12
 * 全套源码已对账，字段顺序无差异。
 */

struct cur {
    const u8 *base;
    size_t   len;
    size_t   pos;
};

static int cur_eof(struct cur *c, size_t n)
{
    return (c->pos + n > c->len) ? -EINVAL : 0;
}

static int cur_u32(struct cur *c, u32 *out)
{
    if (cur_eof(c, 4)) return -EINVAL;
    *out = read_le32(c->base + c->pos);
    c->pos += 4;
    return 0;
}

static int cur_skip(struct cur *c, size_t n)
{
    if (cur_eof(c, n)) return -EINVAL;
    c->pos += n;
    return 0;
}

static int cur_bytes(struct cur *c, const u8 **out, size_t n)
{
    if (cur_eof(c, n)) return -EINVAL;
    *out = c->base + c->pos;
    c->pos += n;
    return 0;
}

/* ebitmap: [mapsize=64][highbit][count] + count × (u32 + u64) */
static int skip_ebitmap(struct cur *c)
{
    u32 mapsize, highbit, count;
    int rc;

    if ((rc = cur_u32(c, &mapsize))) return rc;
    if ((rc = cur_u32(c, &highbit))) return rc;
    if ((rc = cur_u32(c, &count))) return rc;
    if (mapsize == 0 || count > (1u << 20))
        return -EINVAL;
    return cur_skip(c, (size_t)count * 12);
}

static int skip_mls_level(struct cur *c)
{
    int rc;
    if ((rc = cur_skip(c, 4))) return rc;
    return skip_ebitmap(c);
}

/*
 * mls_range_helper: items_m1=1 表 low==high，=2 表有 high。
 * 流: items_m1 + items_m1 × sens + items_m1 × ebitmap。
 */
static int skip_mls_range(struct cur *c)
{
    u32 m1;
    int rc;
    bool has_high;

    if ((rc = cur_u32(c, &m1))) return rc;
    if (m1 != 1 && m1 != 2) return -EINVAL;
    has_high = (m1 == 2);

    if ((rc = cur_skip(c, 4))) return rc;          /* sens_low */
    if (has_high && (rc = cur_skip(c, 4))) return rc;
    if ((rc = skip_ebitmap(c))) return rc;         /* cat_low */
    if (has_high && (rc = skip_ebitmap(c))) return rc;
    return 0;
}

static int skip_type_set(struct cur *c)
{
    int rc;
    if ((rc = skip_ebitmap(c))) return rc;
    if ((rc = skip_ebitmap(c))) return rc;
    return cur_skip(c, 4);
}

static int skip_cons_expr(struct cur *c, u32 vers)
{
    u32 et, attr, op;
    int rc;

    if ((rc = cur_u32(c, &et))) return rc;
    if ((rc = cur_u32(c, &attr))) return rc;
    if ((rc = cur_u32(c, &op))) return rc;

    if (et == CEXPR_NAMES) {
        if ((rc = skip_ebitmap(c))) return rc;
        if (vers >= V_CONSTRAINT_NAMES && (rc = skip_type_set(c)))
            return rc;
    }
    return 0;
}

static int skip_cons_node(struct cur *c, u32 vers)
{
    u32 perms, n, i;
    int rc;

    if ((rc = cur_u32(c, &perms))) return rc;
    if ((rc = cur_u32(c, &n))) return rc;
    if (n > (1u << 20)) return -EINVAL;
    for (i = 0; i < n; i++)
        if ((rc = skip_cons_expr(c, vers))) return rc;
    return 0;
}

static int skip_cons_list(struct cur *c, u32 vers, u32 nlist)
{
    u32 i;
    int rc;
    if (nlist > (1u << 20)) return -EINVAL;
    for (i = 0; i < nlist; i++)
        if ((rc = skip_cons_node(c, vers))) return rc;
    return 0;
}

/* perm: [len, value] + name */
static int skip_perm(struct cur *c)
{
    u32 len, value;
    int rc;

    if ((rc = cur_u32(c, &len))) return rc;
    if ((rc = cur_u32(c, &value))) return rc;
    if (len == 0 || len > NAME_MAX_LEN) return -EINVAL;
    return cur_skip(c, len);
}

/* common: [len, value, perms.nprim, perms.nel] + name + nel × perm */
static int skip_common(struct cur *c)
{
    u32 len, value, nprim, nel, i;
    int rc;

    if ((rc = cur_u32(c, &len))) return rc;
    if ((rc = cur_u32(c, &value))) return rc;
    if ((rc = cur_u32(c, &nprim))) return rc;
    if ((rc = cur_u32(c, &nel))) return rc;
    if (len == 0 || len > NAME_MAX_LEN) return -EINVAL;
    if (nel > 256) return -EINVAL;
    if ((rc = cur_skip(c, len))) return rc;
    for (i = 0; i < nel; i++)
        if ((rc = skip_perm(c))) return rc;
    return 0;
}

/*
 * class: 6-u32 head + name + opt comkey + perms + constraints + validatetrans
 *        + default_user/role/range@v≥27 + default_type@v≥28
 */
static int parse_class(struct cur *c, u32 vers, struct nametab *out)
{
    u32 len, len2, value, nprim, nel, ncons, ncons2, i;
    const u8 *name;
    int rc;

    if ((rc = cur_u32(c, &len)))   return rc;
    if ((rc = cur_u32(c, &len2)))  return rc;
    if ((rc = cur_u32(c, &value))) return rc;
    if ((rc = cur_u32(c, &nprim))) return rc;
    if ((rc = cur_u32(c, &nel)))   return rc;
    if ((rc = cur_u32(c, &ncons))) return rc;
    if (len == 0 || len > NAME_MAX_LEN || len2 > NAME_MAX_LEN ||
        nel > 256 || ncons > (1u << 16))
        return -EINVAL;

    if ((rc = cur_bytes(c, &name, len))) return rc;
    for (i = 0; i < len; i++)
        if (!is_name_char((char)name[i])) return -EINVAL;
    if ((rc = ntab_add(out, (const char *)name, len)) == -ENOMEM)
        return rc;

    if (len2 && (rc = cur_skip(c, len2))) return rc;
    for (i = 0; i < nel; i++)
        if ((rc = skip_perm(c))) return rc;

    if ((rc = skip_cons_list(c, vers, ncons))) return rc;

    if ((rc = cur_u32(c, &ncons2))) return rc;
    if ((rc = skip_cons_list(c, vers, ncons2))) return rc;

    if (vers >= V_NEW_OBJECT_DEFAULTS && (rc = cur_skip(c, 12)))
        return rc;
    if (vers >= V_DEFAULT_TYPE && (rc = cur_skip(c, 4)))
        return rc;
    return 0;
}

/* role: [len, value, bounds@v≥24] + name + ebitmap(dominates) + ebitmap(types) */
static int parse_role(struct cur *c, u32 vers, struct nametab *out)
{
    u32 len, value, bounds;
    const u8 *name;
    u32 i;
    int rc;

    if ((rc = cur_u32(c, &len)))   return rc;
    if ((rc = cur_u32(c, &value))) return rc;
    if (vers >= V_BOUNDARY && (rc = cur_u32(c, &bounds))) return rc;
    if (len == 0 || len > NAME_MAX_LEN) return -EINVAL;

    if ((rc = cur_bytes(c, &name, len))) return rc;
    for (i = 0; i < len; i++)
        if (!is_name_char((char)name[i])) return -EINVAL;
    if ((rc = ntab_add(out, (const char *)name, len)) == -ENOMEM)
        return rc;

    if ((rc = skip_ebitmap(c))) return rc;
    return skip_ebitmap(c);
}

/*
 * type: vers≥24 [len, value, properties, bounds] + name
 *       vers<24 [len, value, primary]           + name
 * primary 才入表——KSU 跟 attribute/alias 也对齐。
 */
static int parse_type(struct cur *c, u32 vers, struct nametab *out)
{
    u32 len, value, third, bounds = 0;
    const u8 *name;
    u32 i;
    int rc;
    bool primary;

    if ((rc = cur_u32(c, &len)))   return rc;
    if ((rc = cur_u32(c, &value))) return rc;
    if ((rc = cur_u32(c, &third))) return rc;
    if (vers >= V_BOUNDARY) {
        if ((rc = cur_u32(c, &bounds))) return rc;
        primary = (third & TYPEDATUM_PRIMARY) &&
                  !(third & (TYPEDATUM_ATTRIBUTE | TYPEDATUM_ALIAS));
    } else {
        primary = (third == 1);
    }
    if (len == 0 || len > NAME_MAX_LEN) return -EINVAL;

    if ((rc = cur_bytes(c, &name, len))) return rc;
    for (i = 0; i < len; i++)
        if (!is_name_char((char)name[i])) return -EINVAL;
    if (primary && (rc = ntab_add(out, (const char *)name, len)) == -ENOMEM)
        return rc;
    return 0;
}

/*
 * user: [len, value, bounds@v≥24] + name + ebitmap(roles) + mls_range + mls_level
 * mls_range/mls_level 是无条件写出的，与 policy.mls_enabled 无关。
 */
static int parse_user(struct cur *c, u32 vers, struct nametab *out)
{
    u32 len, value, bounds;
    const u8 *name;
    u32 i;
    int rc;

    if ((rc = cur_u32(c, &len)))   return rc;
    if ((rc = cur_u32(c, &value))) return rc;
    if (vers >= V_BOUNDARY && (rc = cur_u32(c, &bounds))) return rc;
    if (len == 0 || len > NAME_MAX_LEN) return -EINVAL;

    if ((rc = cur_bytes(c, &name, len))) return rc;
    for (i = 0; i < len; i++)
        if (!is_name_char((char)name[i])) return -EINVAL;
    if ((rc = ntab_add(out, (const char *)name, len)) == -ENOMEM)
        return rc;

    if ((rc = skip_ebitmap(c))) return rc;
    if ((rc = skip_mls_range(c))) return rc;
    return skip_mls_level(c);
}

/* cond_bool: [value, state, len] + name */
static int skip_bool(struct cur *c)
{
    u32 v, st, len;
    int rc;
    if ((rc = cur_u32(c, &v))) return rc;
    if ((rc = cur_u32(c, &st))) return rc;
    if ((rc = cur_u32(c, &len))) return rc;
    if (len == 0 || len > NAME_MAX_LEN) return -EINVAL;
    return cur_skip(c, len);
}

/* sens: [len, isalias] + name + mls_level */
static int skip_sens(struct cur *c)
{
    u32 len, isalias;
    int rc;
    if ((rc = cur_u32(c, &len))) return rc;
    if ((rc = cur_u32(c, &isalias))) return rc;
    if (len == 0 || len > NAME_MAX_LEN) return -EINVAL;
    if ((rc = cur_skip(c, len))) return rc;
    return skip_mls_level(c);
}

/* cat: [len, value, isalias] + name */
static int skip_cat(struct cur *c)
{
    u32 len, value, isalias;
    int rc;
    if ((rc = cur_u32(c, &len))) return rc;
    if ((rc = cur_u32(c, &value))) return rc;
    if ((rc = cur_u32(c, &isalias))) return rc;
    if (len == 0 || len > NAME_MAX_LEN) return -EINVAL;
    return cur_skip(c, len);
}

static int parse_sym_entry(struct cur *c, u32 vers, int sym_id)
{
    switch (sym_id) {
    case SYM_COMMONS: return skip_common(c);
    case SYM_CLASSES: return parse_class(c, vers, &state.classes);
    case SYM_ROLES:   return parse_role(c, vers, &state.roles);
    case SYM_TYPES:   return parse_type(c, vers, &state.types);
    case SYM_USERS:   return parse_user(c, vers, &state.users);
    case SYM_BOOLS:   return skip_bool(c);
    case SYM_LEVELS:  return skip_sens(c);
    case SYM_CATS:    return skip_cat(c);
    default:          return -EINVAL;
    }
}

static int parse_policydb(const void *blob, size_t blen, u32 vers)
{
    struct cur c;
    u32 magic, slen, vers2, config, sym_num, ocon_num;
    u32 sym_id, nprim, nel, i;
    int rc;

    if (!blob || blen < POLICY_MIN_LEN)
        return -EINVAL;
    c.base = blob; c.len = blen; c.pos = 0;

    if ((rc = cur_u32(&c, &magic))) return rc;
    if (magic != POLICY_MAGIC) return -EINVAL;
    if ((rc = cur_u32(&c, &slen))) return rc;
    if (slen != lib_strlen(POLICY_MAGIC_STR)) return -EINVAL;
    if ((rc = cur_skip(&c, slen))) return rc;
    if ((rc = cur_u32(&c, &vers2))) return rc;
    if (vers2 != vers) return -EINVAL;

    if ((rc = cur_u32(&c, &config))) return rc;
    if ((rc = cur_u32(&c, &sym_num))) return rc;
    if ((rc = cur_u32(&c, &ocon_num))) return rc;
    if (sym_num == 0 || sym_num > SYM_NUM_MAX) return -EINVAL;
    (void)config;

    if (vers >= V_POLCAP && (rc = skip_ebitmap(&c))) return rc;
    if (vers >= V_PERMISSIVE && (rc = skip_ebitmap(&c))) return rc;

    for (sym_id = 0; sym_id < sym_num; sym_id++) {
        if ((rc = cur_u32(&c, &nprim))) return rc;
        if ((rc = cur_u32(&c, &nel))) return rc;
        if (nel > 65536u) return -EINVAL;
        for (i = 0; i < nel; i++)
            if ((rc = parse_sym_entry(&c, vers, (int)sym_id))) return rc;
    }
    return 0;
}

/* policydb header 验证（仅用于 capture_baseline 的快速早退） */
static int parse_policy_header(const void *data, size_t len, u32 *vers)
{
    const u8 *p = data;
    u32 slen;

    if (!data || !vers || len < POLICY_MIN_LEN) return -EINVAL;
    if (read_le32(p) != POLICY_MAGIC) return -EINVAL;
    slen = read_le32(p + 4);
    if (slen != lib_strlen(POLICY_MAGIC_STR)) return -EINVAL;
    if (8 + slen + 4 > len) return -EINVAL;
    if (lib_memcmp(p + 8, POLICY_MAGIC_STR, slen)) return -EINVAL;
    *vers = read_le32(p + 8 + slen);
    return 0;
}

/* ===== hook callbacks ===== */

static bool context_valid(const char *ctx, size_t len)
{
    const char *u = NULL, *r = NULL, *t = NULL;
    size_t ul = 0, rl = 0, tl = 0;

    if (!smp_load_acquire(&state.captured))
        return false;
    if (extract_tuple(ctx, len, &u, &ul, &r, &rl, &t, &tl))
        return false;
    if (!ntab_has(&state.users, u, ul)) return false;
    if (!ntab_has(&state.roles, r, rl)) return false;
    return ntab_has(&state.types, t, tl);
}

struct access_view {
    bool both_valid;
};

static int inspect_access(const char *buf, size_t size, struct access_view *out)
{
    const char *scon, *tcon;
    size_t scon_len, tcon_len;
    const char *cur, *end;

    lib_memset(out, 0, sizeof(*out));
    if (!buf || !size) return -EINVAL;

    cur = buf; end = buf + size;
    if (next_token(&cur, end, &scon, &scon_len)) return -EINVAL;
    if (next_token(&cur, end, &tcon, &tcon_len)) return -EINVAL;

    out->both_valid = context_valid(scon, scon_len) &&
                      context_valid(tcon, tcon_len);
    return 0;
}

/*
 * sel_write_context: 永不透传到原函数。baseline 元组校验通过 → fake success；
 * 不通过 → EINVAL。返回 size 时剥掉末尾 NUL 以对齐上游 canonical 长度返回。
 */
static void before_write_context(hook_fargs3_t *args, void *udata)
{
    char  *buf  = (char *)args->arg1;
    size_t size = (size_t)args->arg2;
    size_t reply;

    if (current_uid() < APP_UID_MIN)
        return;

    args->skip_origin = 1;

    if (!smp_load_acquire(&state.captured) || !context_valid(buf, size)) {
        args->ret = -EINVAL;
        return;
    }

    reply = size;
    if (reply && buf[reply - 1] == '\0')
        reply--;
    args->ret = (long)reply;
}

/*
 * 全 deny 但 seqno 从 baseline 派生，避开"固定 1"指纹。
 * allowed=0、auditdeny=0xffffffff 跟 avd_init() 基线一致。
 * buf 容量来自 simple_transaction_get() (PAGE_SIZE)，不是 args->arg2；
 * 用本地 64-byte 缓冲先成型再 memcpy 规避 args->arg2 截断风险。
 */
static void emit_av_deny(char *buf, hook_fargs3_t *args)
{
    char tmp[64];
    u32 seqno;
    int n;

    if (!buf) {
        args->ret = -EINVAL;
        args->skip_origin = 1;
        return;
    }

    seqno = ((state.policy_vers & 0xffffu) << 16) |
            ((u32)state.policy_len & 0xffffu);
    n = snprintf(tmp, sizeof(tmp), "%x %x %x %x %u %x",
                 0u, 0xffffffffu, 0u, 0xffffffffu, seqno, 0u);
    if (n <= 0 || n >= (int)sizeof(tmp)) {
        args->ret = -EINVAL;
        args->skip_origin = 1;
        return;
    }
    lib_memcpy(buf, tmp, (size_t)n);
    args->ret = (long)n;
    args->skip_origin = 1;
}

static void before_write_access(hook_fargs3_t *args, void *udata)
{
    char  *buf  = (char *)args->arg1;
    size_t size = (size_t)args->arg2;
    struct access_view v;

    if (current_uid() < APP_UID_MIN)
        return;

    if (!smp_load_acquire(&state.captured)) {
        emit_av_deny(buf, args);
        return;
    }

    if (inspect_access(buf, size, &v) || !v.both_valid) {
        args->ret = -EINVAL;
        args->skip_origin = 1;
        return;
    }

    emit_av_deny(buf, args);
}

static void handle_setprocattr(const char *name, void *value, size_t size,
                               hook_fargs0_t *args)
{
    if (current_uid() < APP_UID_MIN)
        return;
    if (!name || lib_strcmp(name, "current"))
        return;
    if (!smp_load_acquire(&state.captured) ||
        !context_valid((const char *)value, size)) {
        args->ret = -EINVAL;
        args->skip_origin = 1;
    }
}

static bool str_equals_at(unsigned long addr, const char *expect)
{
    size_t elen;
    const char *p;

    if (!addr || addr < 4096 || is_bad_address((void *)addr))
        return false;
    elen = lib_strlen(expect);
    p = (const char *)addr;
    if (lib_strncmp(p, expect, elen)) return false;
    return p[elen] == '\0';
}

/*
 * security_setprocattr 4.9 是 4 参 (task, name, value, size)，4.14+ 是
 * 3 参 (name, value, size)。靠 "current" 字符串落在哪个槽位识别形态。
 */
static void before_setprocattr_universal(hook_fargs4_t *args, void *udata)
{
    const char *name;
    void  *value;
    size_t size;

    if (str_equals_at((unsigned long)args->arg0, "current")) {
        name  = (const char *)args->arg0;
        value = (void *)args->arg1;
        size  = (size_t)args->arg2;
    } else if (str_equals_at((unsigned long)args->arg1, "current")) {
        name  = (const char *)args->arg1;
        value = (void *)args->arg2;
        size  = (size_t)args->arg3;
    } else {
        return;
    }
    handle_setprocattr(name, value, size, (hook_fargs0_t *)args);
}

/* baseline 抓取 */

static void capture_baseline(void *data, size_t len)
{
    void *copy;
    u32 vers;
    int rc;

    if (smp_load_acquire(&state.captured))
        return;
    if (atomic_cmpxchg(&state.capturing, 0, 1) != 0)
        return;

    if (!data || is_bad_address(data)) goto out;
    if (len < POLICY_MIN_LEN || len > POLICY_MAX_LEN) goto out;

    if (parse_policy_header(data, len, &vers)) {
        log_boot("selinux_hide: bad policy header\n");
        goto out;
    }

    copy = vmalloc(len);
    if (!copy) {
        log_boot("selinux_hide: vmalloc(%zu) failed\n", len);
        goto out;
    }
    lib_memcpy(copy, data, len);

    if (ntab_alloc(&state.types,   NTAB_BIG_ENTRIES,   NTAB_BIG_NAMES_MAX) ||
        ntab_alloc(&state.users,   NTAB_SMALL_ENTRIES, NTAB_SMALL_NAMES_MAX) ||
        ntab_alloc(&state.roles,   NTAB_SMALL_ENTRIES, NTAB_SMALL_NAMES_MAX) ||
        ntab_alloc(&state.classes, NTAB_SMALL_ENTRIES, NTAB_SMALL_NAMES_MAX)) {
        log_boot("selinux_hide: nametab alloc failed\n");
        goto err;
    }

    rc = parse_policydb(copy, len, vers);
    if (rc) {
        log_boot("selinux_hide: parse_policydb rc=%d\n", rc);
        goto err;
    }

    state.policy_raw  = copy;
    state.policy_len  = len;
    state.policy_vers = vers;
    smp_store_release(&state.captured, true);

    log_boot("selinux_hide: baseline len=%zu vers=%u "
             "types=%u users=%u roles=%u classes=%u\n",
             len, vers, state.types.count, state.users.count,
             state.roles.count, state.classes.count);
    goto out;

err:
    ntab_free(&state.types);
    ntab_free(&state.users);
    ntab_free(&state.roles);
    ntab_free(&state.classes);
    vfree(copy);
out:
    atomic_set(&state.capturing, 0);
}

static bool has_policy_magic(unsigned long ptr)
{
    if (!ptr || ptr < 4096 || is_bad_address((void *)ptr))
        return false;
    return read_le32((const void *)ptr) == POLICY_MAGIC;
}

/*
 * security_load_policy 跨版本两种形态：
 *   (data, len, ...)         4.9 / 6.12
 *   (state, data, len, ...)  4.14..6.6
 * 用 arg0 处是否带 sepolicy magic 区分。
 */
static void after_load_policy_universal(hook_fargs4_t *args, void *udata)
{
    if ((long)args->ret < 0)
        return;

    if (has_policy_magic((unsigned long)args->arg0))
        capture_baseline((void *)args->arg0, (size_t)args->arg1);
    else
        capture_baseline((void *)args->arg1, (size_t)args->arg2);
}

/* ===== security_read_policy hook =====
 * 替换 /sys/fs/selinux/policy 读出的字节流为 baseline blob。
 */

static bool arg_is_selinux_state(unsigned long arg)
{
    unsigned long sa = (unsigned long)kvar(selinux_state);
    return sa && arg == sa;
}

static bool read_policy_slot_valid(void **data_p, size_t *len_p)
{
    unsigned long a, b, d;

    if (!data_p || !len_p) return false;
    if ((unsigned long)data_p < 4096 || (unsigned long)len_p < 4096) return false;
    if ((void *)data_p == (void *)len_p) return false;
    if (is_bad_address((void *)data_p) || is_bad_address((void *)len_p))
        return false;
    /* caller plm 由 kzalloc 分配，调用前必须 *data==NULL && *len==0 */
    if (*data_p || *len_p) return false;
    /* 同 struct 相邻字段，距离不会超过 64 */
    a = (unsigned long)data_p;
    b = (unsigned long)len_p;
    d = a > b ? a - b : b - a;
    return d <= 64;
}

/*
 * security_read_policy 形态:
 *   (void **data, size_t *len)            4.9 / 4.14 上游 / 6.4+
 *   (selinux_state *, void **data, ...)   4.14 OEM 回迁 / 4.19..6.3
 * 不按 minor 判别（OEM 平移会反转）；先用 selinux_state 全局地址锁定，
 * 锁不到再用槽位语义校验依次试 (arg0,arg1) / (arg1,arg2)。
 */
static int resolve_read_policy_args(hook_fargs4_t *args,
                                    void ***pp_data, size_t **pp_len)
{
    void **dp;
    size_t *lp;

    if (!args || !pp_data || !pp_len) return -EINVAL;

    if (arg_is_selinux_state((unsigned long)args->arg0)) {
        dp = (void **)args->arg1;
        lp = (size_t *)args->arg2;
        if (!read_policy_slot_valid(dp, lp)) return -EINVAL;
        *pp_data = dp; *pp_len = lp;
        return 0;
    }

    dp = (void **)args->arg0;
    lp = (size_t *)args->arg1;
    if (read_policy_slot_valid(dp, lp)) {
        *pp_data = dp; *pp_len = lp;
        return 0;
    }

    dp = (void **)args->arg1;
    lp = (size_t *)args->arg2;
    if (read_policy_slot_valid(dp, lp)) {
        *pp_data = dp; *pp_len = lp;
        return 0;
    }
    return -EINVAL;
}

/*
 * sel_open_policy 调用 security_read_policy 把 live policy 序列化到 plm，
 * 后续 read/mmap 都从 plm->data 取。这里直接换 baseline 副本，
 * 由 sel_release_policy 走 vfree 收尾——必须用 vmalloc_user。
 */
static void before_read_policy_universal(hook_fargs4_t *args, void *udata)
{
    static atomic_t once_ok = ATOMIC_INIT(0);
    static atomic_t once_fail = ATOMIC_INIT(0);
    void **data_p;
    size_t *len_p;
    void *copy;

    if (current_uid() < APP_UID_MIN)
        return;
    if (!smp_load_acquire(&state.captured))
        return;
    if (!state.policy_raw || !state.policy_len)
        return;

    if (resolve_read_policy_args(args, &data_p, &len_p)) {
        args->ret = -EINVAL;
        args->skip_origin = 1;
        if (atomic_cmpxchg(&once_fail, 0, 1) == 0)
            log_boot("selinux_hide: /policy fail-closed: args unresolved\n");
        return;
    }

    copy = vmalloc_user(state.policy_len);
    if (!copy) {
        args->ret = -ENOMEM;
        args->skip_origin = 1;
        return;
    }
    lib_memcpy(copy, state.policy_raw, state.policy_len);
    *data_p = copy;
    *len_p  = state.policy_len;
    args->ret = 0;
    args->skip_origin = 1;

    if (atomic_cmpxchg(&once_ok, 0, 1) == 0)
        log_boot("selinux_hide: /policy substituted with baseline len=%zu\n",
                 state.policy_len);
}

/* ===== install / uninstall =====
 *
 * 注意 5.10 GKI 起内核开启 CFI：write_op[i] 存的是 sel_write_*.cfi_jt 项，
 * 不是真函数地址；之前靠 scan write_op 找 SEL_CONTEXT/SEL_ACCESS 槽位的做法
 * 在 CFI 下完全失效。kallsyms 解析到的是真函数入口，hook_wrap3 patch 入口
 * 指令后无论调用者走 cfi_jt 还是直跳都能拦截，所以直接 hook 真函数最稳。
 */

static int install_write_op_hooks(void)
{
    void *ctx_fn, *acc_fn;
    hook_err_t err;

    ctx_fn = (void *)kallsyms_lookup_name("sel_write_context");
    acc_fn = (void *)kallsyms_lookup_name("sel_write_access");
    if (!ctx_fn || !acc_fn) {
        log_boot("selinux_hide: sel_write_context=%px sel_write_access=%px\n",
                 ctx_fn, acc_fn);
        return -ENOSYS;
    }

    err = hook_wrap3(ctx_fn, before_write_context, NULL, NULL);
    if (err != HOOK_NO_ERR) {
        log_boot("selinux_hide: hook context: %d\n", err);
        return -EINVAL;
    }
    state.orig_context_write = ctx_fn;

    err = hook_wrap3(acc_fn, before_write_access, NULL, NULL);
    if (err != HOOK_NO_ERR) {
        log_boot("selinux_hide: hook access: %d\n", err);
        hook_unwrap(ctx_fn, before_write_context, NULL);
        state.orig_context_write = NULL;
        return -EINVAL;
    }
    state.orig_access_write = acc_fn;
    return 0;
}

static int install_setprocattr_hook(void)
{
    void *addr = (void *)kfunc(security_setprocattr);
    hook_err_t err;

    if (!addr) {
        log_boot("selinux_hide: security_setprocattr unresolved\n");
        return -ENOSYS;
    }
    err = hook_wrap4(addr, before_setprocattr_universal, NULL, NULL);
    if (err != HOOK_NO_ERR) {
        log_boot("selinux_hide: hook setprocattr: %d\n", err);
        return -EINVAL;
    }
    state.orig_setprocattr = addr;
    return 0;
}

static int install_load_policy_hook(void)
{
    void *addr = (void *)kfunc(security_load_policy);
    hook_err_t err;

    if (!addr) {
        log_boot("selinux_hide: security_load_policy unresolved\n");
        return -ENOSYS;
    }
    err = hook_wrap4(addr, NULL, after_load_policy_universal, NULL);
    if (err != HOOK_NO_ERR) {
        log_boot("selinux_hide: hook load_policy: %d\n", err);
        return -EINVAL;
    }
    state.orig_load_policy = addr;
    return 0;
}

static int install_read_policy_hook(void)
{
    void *addr = (void *)kfunc(security_read_policy);
    hook_err_t err;

    if (!addr) {
        log_boot("selinux_hide: security_read_policy unresolved\n");
        return -ENOSYS;
    }
    err = hook_wrap4(addr, before_read_policy_universal, NULL, NULL);
    if (err != HOOK_NO_ERR) {
        log_boot("selinux_hide: hook read_policy: %d\n", err);
        return -EINVAL;
    }
    state.orig_read_policy = addr;
    return 0;
}

static int install_all(void)
{
    int rc;

    if (state.installed)
        return 0;

    rc = install_write_op_hooks();
    if (rc)
        return rc;

    /* 这三个挂不上不致命，主路径已由 write_op hook 覆盖 */
    rc = install_setprocattr_hook();
    if (rc) log_boot("selinux_hide: setprocattr skipped (%d)\n", rc);
    rc = install_load_policy_hook();
    if (rc) log_boot("selinux_hide: load_policy skipped (%d)\n", rc);
    rc = install_read_policy_hook();
    if (rc) log_boot("selinux_hide: read_policy skipped (%d)\n", rc);

    state.installed = true;
    log_boot("selinux_hide: ready\n");
    return 0;
}

int kpatch_selinux_hide_init(void)    { return install_all(); }
int kpatch_selinux_hide_prepare(void) { return install_all(); }

void kpatch_selinux_hide_exit(void)
{
    if (!state.installed)
        goto reset;

    if (state.orig_context_write)
        hook_unwrap(state.orig_context_write, before_write_context, NULL);
    if (state.orig_access_write)
        hook_unwrap(state.orig_access_write, before_write_access, NULL);
    if (state.orig_setprocattr)
        hook_unwrap(state.orig_setprocattr,
                    (void *)before_setprocattr_universal, NULL);
    if (state.orig_load_policy)
        hook_unwrap(state.orig_load_policy,
                    NULL, (void *)after_load_policy_universal);
    if (state.orig_read_policy)
        hook_unwrap(state.orig_read_policy,
                    (void *)before_read_policy_universal, NULL);

reset:
    ntab_free(&state.types);
    ntab_free(&state.users);
    ntab_free(&state.roles);
    ntab_free(&state.classes);
    if (state.policy_raw) {
        vfree(state.policy_raw);
        state.policy_raw = NULL;
    }
    lib_memset(&state, 0, sizeof(state));
    log_boot("selinux_hide: gone\n");
}
