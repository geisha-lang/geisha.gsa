#include <stddef.h>
#include <stdint.h>

/*
 * Freestanding WebAssembly (`wasm32-unknown-unknown`) runtime for Geisha
 * with self-describing segmented Mark-Sweep GC (`gs_wasm_gc_collect`)
 * and O(1) size-segregated free lists.
 *
 * Compiles with `clang --target=wasm32 -O2 -nostdlib -ffreestanding -c` (zero libc needed).
 */

extern unsigned char __heap_base;

#define WASM_PAGE_BYTES   65536u
#define SEG_DEFAULT_BYTES (4u * WASM_PAGE_BYTES) /* 256 KB per segment */
#define NUM_FREE_BINS     16u
#define MAX_WASM_ROOTS    2048u
#define MARK_STACK_CAP    4096u

/* 8-byte object header stored immediately before every 8-byte-aligned payload */
#define HDR_ALLOC_BIT   1ULL
#define HDR_MARK_BIT    2ULL
#define HDR_NOSCAN_BIT  4ULL
#define HDR_SIZE_MASK   (~7ULL)

typedef struct wasm_free_t {
    uint32_t size; /* total bytes (multiple of 8, >= 8) */
    struct wasm_free_t *next;
} wasm_free_t;

typedef struct wasm_seg_t {
    struct wasm_seg_t *next;
    uint32_t payload_base;
    uint32_t payload_end;
    uint32_t bitmap_words;
    uint32_t alloc_bits[]; /* 1 bit per 8-byte slot in [payload_base, payload_end) */
} wasm_seg_t;

static uintptr_t gs_raw_cursor = 0;
static uintptr_t gs_raw_end = 0;

static wasm_seg_t *gs_segs = NULL;
static uint32_t gs_min_addr = 0xFFFFFFFFu;
static uint32_t gs_max_addr = 0;

static wasm_free_t *gs_free_bins[NUM_FREE_BINS];
static uint32_t gs_free_mask = 0;

static uint32_t gs_live_bytes = 0;
static uint32_t gs_total_seg_bytes = 0;

static void **gs_roots[MAX_WASM_ROOTS];
static uint32_t gs_root_count = 0;

static uint32_t gs_mark_stack[MARK_STACK_CAP];

static inline uint32_t align8(uint32_t n)
{
    return (n + 7u) & ~7u;
}

static inline uint32_t free_bin_index(uint32_t bytes)
{
    uint32_t units = bytes >> 3; /* 8-byte units, >= 1 */
    if (units < 2u) return 0u;
    uint32_t b = 31u - (uint32_t)__builtin_clz(units);
    return (b >= NUM_FREE_BINS) ? (NUM_FREE_BINS - 1u) : b;
}

static inline void free_list_clear(void)
{
    for (uint32_t i = 0; i < NUM_FREE_BINS; i++) {
        gs_free_bins[i] = NULL;
    }
    gs_free_mask = 0;
}

static inline void free_list_insert(uint32_t addr, uint32_t bytes)
{
    if (bytes < 8u) return;
    uint32_t b = free_bin_index(bytes);
    wasm_free_t *node = (wasm_free_t *)(uintptr_t)addr;
    node->size = bytes;
    node->next = gs_free_bins[b];
    gs_free_bins[b] = node;
    gs_free_mask |= (1u << b);
}

static void gs_raw_ensure_init(void)
{
    if (gs_raw_cursor == 0) {
        gs_raw_cursor = ((uintptr_t)&__heap_base + 7u) & ~(uintptr_t)7u;
        gs_raw_end = (uintptr_t)__builtin_wasm_memory_size(0) * WASM_PAGE_BYTES;
    }
}

static void *gs_raw_bump(uint32_t bytes)
{
    gs_raw_ensure_init();
    bytes = align8(bytes);
    if (gs_raw_cursor + bytes > gs_raw_end) {
        uint32_t need = (uint32_t)((gs_raw_cursor + bytes) - gs_raw_end);
        uint32_t pages = (need + WASM_PAGE_BYTES - 1u) / WASM_PAGE_BYTES;
        if (pages < 4u) pages = 4u;
        int32_t prev = (int32_t)__builtin_wasm_memory_grow(0, pages);
        if (prev < 0) {
            __builtin_trap();
        }
        gs_raw_end = (uintptr_t)__builtin_wasm_memory_size(0) * WASM_PAGE_BYTES;
    }
    void *ptr = (void *)gs_raw_cursor;
    gs_raw_cursor += bytes;
    return ptr;
}

static wasm_seg_t *alloc_segment(uint32_t min_payload_bytes)
{
    uint32_t payload_bytes = SEG_DEFAULT_BYTES;
    if (min_payload_bytes > payload_bytes) {
        payload_bytes = (min_payload_bytes + WASM_PAGE_BYTES - 1u) & ~(WASM_PAGE_BYTES - 1u);
    }
    uint32_t num_slots = payload_bytes >> 3;
    uint32_t bitmap_words = (num_slots + 31u) >> 5;
    uint32_t meta_bytes = align8((uint32_t)sizeof(wasm_seg_t) + bitmap_words * 4u);
    uint32_t total_bytes = meta_bytes + payload_bytes;

    unsigned char *raw = (unsigned char *)gs_raw_bump(total_bytes);
    wasm_seg_t *seg = (wasm_seg_t *)(void *)raw;
    seg->next = gs_segs;
    seg->payload_base = (uint32_t)(uintptr_t)(raw + meta_bytes);
    seg->payload_end = seg->payload_base + payload_bytes;
    seg->bitmap_words = bitmap_words;
    /* Note: memory from memory.grow is already zeroed, so alloc_bits starts all-zero */

    gs_segs = seg;
    gs_total_seg_bytes += payload_bytes;
    if (seg->payload_base < gs_min_addr) gs_min_addr = seg->payload_base;
    if (seg->payload_end > gs_max_addr) gs_max_addr = seg->payload_end;

    free_list_insert(seg->payload_base, payload_bytes);
    return seg;
}

static inline wasm_seg_t *find_seg_for_hdr(uint32_t hdr_addr)
{
    for (wasm_seg_t *s = gs_segs; s != NULL; s = s->next) {
        if (hdr_addr >= s->payload_base && hdr_addr < s->payload_end) {
            return s;
        }
    }
    return NULL;
}

static uint32_t pickup_free(uint32_t need_bytes, uint32_t *out_bytes)
{
    uint32_t b0 = free_bin_index(need_bytes);

    /* 1. Try exact bin (bounded scan) */
    if (gs_free_mask & (1u << b0)) {
        wasm_free_t **prev = &gs_free_bins[b0];
        wasm_free_t *cur = gs_free_bins[b0];
        int steps = 0;
        while (cur != NULL && steps < 16) {
            if (cur->size >= need_bytes) {
                uint32_t rem = cur->size - need_bytes;
                *prev = cur->next;
                if (gs_free_bins[b0] == NULL) gs_free_mask &= ~(1u << b0);
                uint32_t addr = (uint32_t)(uintptr_t)cur;
                if (rem >= 8u) {
                    free_list_insert(addr + need_bytes, rem);
                    *out_bytes = need_bytes;
                } else {
                    *out_bytes = cur->size;
                }
                return addr;
            }
            prev = &cur->next;
            cur = cur->next;
            steps++;
        }
    }

    /* 2. O(1) pop from smallest strictly larger non-empty bin */
    if (b0 + 1u < NUM_FREE_BINS) {
        uint32_t hi = gs_free_mask & (~0u << (b0 + 1u));
        if (hi != 0u) {
            uint32_t b = (uint32_t)__builtin_ctz(hi);
            wasm_free_t *cur = gs_free_bins[b];
            gs_free_bins[b] = cur->next;
            if (gs_free_bins[b] == NULL) gs_free_mask &= ~(1u << b);
            uint32_t addr = (uint32_t)(uintptr_t)cur;
            uint32_t rem = cur->size - need_bytes;
            if (rem >= 8u) {
                free_list_insert(addr + need_bytes, rem);
                *out_bytes = need_bytes;
            } else {
                *out_bytes = cur->size;
            }
            return addr;
        }
    }

    /* 3. Full scan of exact bin */
    if (gs_free_mask & (1u << b0)) {
        wasm_free_t **prev = &gs_free_bins[b0];
        wasm_free_t *cur = gs_free_bins[b0];
        while (cur != NULL) {
            if (cur->size >= need_bytes) {
                uint32_t rem = cur->size - need_bytes;
                *prev = cur->next;
                if (gs_free_bins[b0] == NULL) gs_free_mask &= ~(1u << b0);
                uint32_t addr = (uint32_t)(uintptr_t)cur;
                if (rem >= 8u) {
                    free_list_insert(addr + need_bytes, rem);
                    *out_bytes = need_bytes;
                } else {
                    *out_bytes = cur->size;
                }
                return addr;
            }
            prev = &cur->next;
            cur = cur->next;
        }
    }

    return 0u;
}

static void *wasm_alloc_impl(int64_t bytes, int noscan)
{
    uint32_t payload_bytes = (bytes <= 0) ? 8u : align8((uint32_t)bytes);
    uint32_t total_bytes = payload_bytes + 8u; /* +8B header */

    uint32_t actual_bytes = total_bytes;
    uint32_t hdr_addr = pickup_free(total_bytes, &actual_bytes);
    if (hdr_addr == 0u) {
        alloc_segment(total_bytes);
        hdr_addr = pickup_free(total_bytes, &actual_bytes);
        if (hdr_addr == 0u) {
            __builtin_trap();
        }
    }

    wasm_seg_t *seg = find_seg_for_hdr(hdr_addr);
    if (seg != NULL) {
        uint32_t slot = (hdr_addr - seg->payload_base) >> 3;
        seg->alloc_bits[slot >> 5] |= (1u << (slot & 31u));
    }

    uint64_t *hdr = (uint64_t *)(uintptr_t)hdr_addr;
    *hdr = ((uint64_t)actual_bytes) | HDR_ALLOC_BIT | (noscan ? HDR_NOSCAN_BIT : 0ULL);
    gs_live_bytes += actual_bytes;

    /* Zero payload so reused freed blocks never leak stale pointers to conservative GC */
    uint64_t *p = hdr + 1;
    uint32_t qwords = (actual_bytes - 8u) >> 3;
    for (uint32_t i = 0; i < qwords; i++) {
        p[i] = 0ULL;
    }
    return (void *)p;
}

void *gc_alloc(int64_t bytes)
{
    return wasm_alloc_impl(bytes, 0);
}

void *gc_alloc_atomic(int64_t bytes)
{
    return wasm_alloc_impl(bytes, 1);
}

void gc_init_with_stack(int64_t heap_words, void *stack_anchor)
{
    (void)heap_words;
    (void)stack_anchor;
    gs_raw_ensure_init();
}

void gc_register_root(void **slot)
{
    if (slot != NULL && gs_root_count < MAX_WASM_ROOTS) {
        gs_roots[gs_root_count++] = slot;
    }
}

/* ---- Frame-boundary Mark-Sweep GC (safe to call from JS between WASM entry points) ---- */

static inline uint32_t find_allocated_hdr(uint32_t payload_ptr)
{
    if (payload_ptr < gs_min_addr + 8u || payload_ptr >= gs_max_addr || (payload_ptr & 7u) != 0u) {
        return 0u;
    }
    uint32_t hdr_addr = payload_ptr - 8u;
    for (wasm_seg_t *s = gs_segs; s != NULL; s = s->next) {
        if (hdr_addr >= s->payload_base && hdr_addr < s->payload_end) {
            uint32_t slot = (hdr_addr - s->payload_base) >> 3;
            if (s->alloc_bits[slot >> 5] & (1u << (slot & 31u))) {
                return hdr_addr;
            }
            return 0u;
        }
    }
    return 0u;
}

static void mark_from_hdr(uint32_t root_hdr, int *overflowed)
{
    uint64_t *rh = (uint64_t *)(uintptr_t)root_hdr;
    if ((*rh & HDR_MARK_BIT) != 0ULL) return;
    *rh |= HDR_MARK_BIT;
    if ((*rh & HDR_NOSCAN_BIT) != 0ULL) return;

    uint32_t sp = 0;
    gs_mark_stack[sp++] = root_hdr;

    while (sp > 0u) {
        uint32_t hdr_addr = gs_mark_stack[--sp];
        uint64_t hdr_val = *(uint64_t *)(uintptr_t)hdr_addr;
        if ((hdr_val & HDR_NOSCAN_BIT) != 0ULL) continue;

        uint32_t total_bytes = (uint32_t)(hdr_val & HDR_SIZE_MASK);
        uint32_t payload_u32s = (total_bytes - 8u) >> 2;
        const uint32_t *fields = (const uint32_t *)(uintptr_t)(hdr_addr + 8u);

        for (uint32_t i = 0; i < payload_u32s; i++) {
            uint32_t child_hdr = find_allocated_hdr(fields[i]);
            if (child_hdr != 0u) {
                uint64_t *ch = (uint64_t *)(uintptr_t)child_hdr;
                if ((*ch & HDR_MARK_BIT) == 0ULL) {
                    *ch |= HDR_MARK_BIT;
                    if ((*ch & HDR_NOSCAN_BIT) == 0ULL) {
                        if (sp < MARK_STACK_CAP) {
                            gs_mark_stack[sp++] = child_hdr;
                        } else {
                            *overflowed = 1;
                        }
                    }
                }
            }
        }
    }
}

__attribute__((export_name("gs_wasm_gc_collect")))
int32_t gs_wasm_gc_collect(void)
{
    int overflowed = 0;

    /* 1. Mark all objects reachable from registered global roots */
    for (uint32_t i = 0; i < gs_root_count; i++) {
        uint32_t ptr_val = (uint32_t)(uintptr_t)(*gs_roots[i]);
        uint32_t hdr_addr = find_allocated_hdr(ptr_val);
        if (hdr_addr != 0u) {
            mark_from_hdr(hdr_addr, &overflowed);
        }
    }

    /* 1b. Handle rare mark-stack overflow by rescanning marked objects to a fixed point */
    while (overflowed) {
        overflowed = 0;
        for (wasm_seg_t *s = gs_segs; s != NULL; s = s->next) {
            uint32_t cur = s->payload_base;
            while (cur < s->payload_end) {
                uint32_t slot = (cur - s->payload_base) >> 3;
                uint32_t word = s->alloc_bits[slot >> 5];
                uint32_t bit = slot & 31u;
                if (bit == 0u && word == 0u) {
                    cur += 32u * 8u;
                    continue;
                }
                if (word & (1u << bit)) {
                    uint64_t hdr_val = *(uint64_t *)(uintptr_t)cur;
                    uint32_t sz = (uint32_t)(hdr_val & HDR_SIZE_MASK);
                    if ((hdr_val & HDR_MARK_BIT) != 0ULL && (hdr_val & HDR_NOSCAN_BIT) == 0ULL) {
                        uint32_t payload_u32s = (sz - 8u) >> 2;
                        const uint32_t *fields = (const uint32_t *)(uintptr_t)(cur + 8u);
                        for (uint32_t j = 0; j < payload_u32s; j++) {
                            uint32_t child_hdr = find_allocated_hdr(fields[j]);
                            if (child_hdr != 0u && ((*(uint64_t *)(uintptr_t)child_hdr) & HDR_MARK_BIT) == 0ULL) {
                                mark_from_hdr(child_hdr, &overflowed);
                            }
                        }
                    }
                    cur += sz;
                } else {
                    uint32_t rem = word >> bit;
                    uint32_t skip = (rem == 0u) ? (32u - bit) : (uint32_t)__builtin_ctz(rem);
                    cur += skip * 8u;
                }
            }
        }
    }

    /* 2. Sweep segments, clear mark bits, and coalesce dead runs into segregated free bins */
    free_list_clear();
    uint32_t prev_live = gs_live_bytes;
    uint32_t new_live = 0;

    for (wasm_seg_t *s = gs_segs; s != NULL; s = s->next) {
        uint32_t cur = s->payload_base;
        uint32_t free_start = 0;
        uint32_t free_bytes = 0;

        while (cur < s->payload_end) {
            uint32_t slot = (cur - s->payload_base) >> 3;
            uint32_t widx = slot >> 5;
            uint32_t bit = slot & 31u;
            uint32_t word = s->alloc_bits[widx];

            if (bit == 0u && word == 0u) {
                if (free_bytes == 0u) free_start = cur;
                free_bytes += 32u * 8u;
                cur += 32u * 8u;
                continue;
            }

            uint32_t mask = 1u << bit;
            if (word & mask) {
                uint64_t *hp = (uint64_t *)(uintptr_t)cur;
                uint64_t hdr_val = *hp;
                uint32_t sz = (uint32_t)(hdr_val & HDR_SIZE_MASK);
                if (hdr_val & HDR_MARK_BIT) {
                    *hp = hdr_val & ~HDR_MARK_BIT;
                    if (free_bytes >= 8u) {
                        free_list_insert(free_start, free_bytes);
                    }
                    free_bytes = 0;
                    new_live += sz;
                } else {
                    s->alloc_bits[widx] &= ~mask;
                    if (free_bytes == 0u) free_start = cur;
                    free_bytes += sz;
                }
                cur += sz;
            } else {
                uint32_t rem = word >> bit;
                uint32_t skip = (rem == 0u) ? (32u - bit) : (uint32_t)__builtin_ctz(rem);
                if (free_bytes == 0u) free_start = cur;
                free_bytes += skip * 8u;
                cur += skip * 8u;
            }
        }

        if (free_bytes >= 8u) {
            free_list_insert(free_start, free_bytes);
        }
    }

    gs_live_bytes = new_live;
    return (int32_t)(prev_live >= new_live ? (prev_live - new_live) : 0u);
}

/* ---- Core string & memory helpers (i64 size ABI matching Geisha LLVM IR) ---- */

int64_t gs_strlen(const char *s)
{
    if (s == NULL) return 0;
    int64_t n = 0;
    while (s[n] != '\0') n++;
    return n;
}

void *gs_memcpy(void *dst, const void *src, int64_t n)
{
    if (n <= 0) return dst;
    unsigned char *d = (unsigned char *)dst;
    const unsigned char *s = (const unsigned char *)src;
    size_t len = (size_t)n;
    /* Word-wise copy when both pointers are 4-byte aligned */
    if ((((uintptr_t)d | (uintptr_t)s) & 3u) == 0u) {
        while (len >= 4u) {
            *(uint32_t *)(void *)d = *(const uint32_t *)(const void *)s;
            d += 4;
            s += 4;
            len -= 4;
        }
    }
    while (len > 0u) {
        *d++ = *s++;
        len--;
    }
    return dst;
}

int32_t gs_str_cmp(const char *a, const char *b)
{
    if (a == b) return 0;
    if (a == NULL) return -1;
    if (b == NULL) return 1;
    while (*a != '\0' && *a == *b) {
        a++;
        b++;
    }
    int diff = (unsigned char)*a - (unsigned char)*b;
    return (diff < 0) ? -1 : (diff > 0 ? 1 : 0);
}

/* ---- Freestanding `strtod` and entropy seed for `std.str` / `std.rand` ---- */

double strtod(const char *s, char **endptr)
{
    if (s == NULL) {
        if (endptr != NULL) *endptr = NULL;
        return 0.0;
    }
    const char *p = s;
    while (*p == ' ' || *p == '\t' || *p == '\n' || *p == '\r') p++;

    int neg = 0;
    if (*p == '-') { neg = 1; p++; }
    else if (*p == '+') { p++; }

    double val = 0.0;
    int any = 0;
    while (*p >= '0' && *p <= '9') {
        val = val * 10.0 + (double)(*p - '0');
        p++;
        any = 1;
    }
    if (*p == '.') {
        p++;
        double scale = 0.1;
        while (*p >= '0' && *p <= '9') {
            val += (double)(*p - '0') * scale;
            scale *= 0.1;
            p++;
            any = 1;
        }
    }
    if (!any) {
        if (endptr != NULL) *endptr = (char *)s;
        return 0.0;
    }
    if (*p == 'e' || *p == 'E') {
        const char *ep = p + 1;
        int eneg = 0;
        if (*ep == '-') { eneg = 1; ep++; }
        else if (*ep == '+') { ep++; }
        int exp = 0;
        int eany = 0;
        while (*ep >= '0' && *ep <= '9') {
            if (exp < 1000) exp = exp * 10 + (*ep - '0');
            ep++;
            eany = 1;
        }
        if (eany) {
            p = ep;
            double factor = 1.0;
            double base = eneg ? 0.1 : 10.0;
            while (exp > 0) {
                if (exp & 1) factor *= base;
                base *= base;
                exp >>= 1;
            }
            val *= factor;
        }
    }
    if (endptr != NULL) *endptr = (char *)p;
    return neg ? -val : val;
}

static uint64_t gs_wasm_seed_counter = 0x243f6a8885a308d3ULL;

int64_t gs_sys_rand_seed(void)
{
    gs_wasm_seed_counter += 0x9e3779b97f4a7c15ULL;
    return (int64_t)gs_wasm_seed_counter;
}

/* ---- Runtime traps ---- */

void gs_match_fail(void) { __builtin_trap(); }
void gs_bounds_fail(int32_t idx, int32_t len) { (void)idx; (void)len; __builtin_trap(); }
void gs_div_zero_fail(void) { __builtin_trap(); }

/* ---- Optional host logging bridge (dropped by --gc-sections if unused) ---- */

__attribute__((import_module("env"), import_name("gs_log")))
extern void gs_wasm_host_log(const char *ptr, int32_t len);

void printLn(const char *s, void *fv)
{
    (void)fv;
    if (s == NULL) {
        gs_wasm_host_log("", 0);
    } else {
        gs_wasm_host_log(s, (int32_t)gs_strlen(s));
    }
}

void putChar(const char c, void *fv)
{
    (void)fv;
    char buf[2];
    buf[0] = c;
    buf[1] = '\0';
    gs_wasm_host_log(buf, 1);
}

void putNumber(const int32_t n, void *fv)
{
    (void)fv;
    char buf[16];
    int32_t pos = 0;
    int64_t v = (int64_t)n;
    if (v < 0) {
        buf[pos++] = '-';
        v = -v;
    }
    char tmp[16];
    int32_t tlen = 0;
    if (v == 0) {
        tmp[tlen++] = '0';
    } else {
        while (v > 0) {
            tmp[tlen++] = (char)('0' + (v % 10));
            v /= 10;
        }
    }
    for (int32_t i = tlen - 1; i >= 0; i--) {
        buf[pos++] = tmp[i];
    }
    gs_wasm_host_log(buf, pos);
}

void putFloat(const double f, void *fv)
{
    (void)f;
    (void)fv;
}

/* ---- JS/WASM interop bridge exports ---- */

__attribute__((export_name("gs_wasm_alloc")))
void *gs_wasm_alloc(int32_t bytes)
{
    return gc_alloc_atomic((int64_t)bytes);
}

__attribute__((export_name("gs_wasm_str_len")))
int32_t gs_wasm_str_len(const char *s)
{
    return (int32_t)gs_strlen(s);
}

__attribute__((export_name("gs_wasm_heap_used")))
int32_t gs_wasm_heap_used(void)
{
    return (int32_t)gs_total_seg_bytes;
}

__attribute__((export_name("gs_wasm_heap_live")))
int32_t gs_wasm_heap_live(void)
{
    return (int32_t)gs_live_bytes;
}
