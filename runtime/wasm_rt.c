#include <stddef.h>
#include <stdint.h>

/*
 * Freestanding WebAssembly (`wasm32-unknown-unknown`) runtime for Geisha.
 * Compiles with `clang --target=wasm32 -O2 -nostdlib -c` (zero libc needed).
 */

extern unsigned char __heap_base;

static uintptr_t gs_heap_cursor = 0;
static uintptr_t gs_heap_end = 0;

static void **gs_roots[1024];
static int32_t gs_root_count = 0;

static void gs_heap_ensure_init(void)
{
    if (gs_heap_cursor == 0) {
        gs_heap_cursor = ((uintptr_t)&__heap_base + 7u) & ~(uintptr_t)7u;
        gs_heap_end = (uintptr_t)__builtin_wasm_memory_size(0) * 65536u;
    }
}

void *gc_alloc(int64_t bytes)
{
    gs_heap_ensure_init();
    size_t sz = (bytes <= 0) ? 8u : (size_t)bytes;
    sz = (sz + 7u) & ~(size_t)7u;

    if (gs_heap_cursor + sz > gs_heap_end) {
        size_t need = (gs_heap_cursor + sz) - gs_heap_end;
        size_t pages = (need + 65535u) / 65536u;
        if (pages < 4u) pages = 4u;
        int32_t prev = (int32_t)__builtin_wasm_memory_grow(0, pages);
        if (prev < 0) {
            __builtin_trap();
        }
        gs_heap_end = (uintptr_t)__builtin_wasm_memory_size(0) * 65536u;
    }

    unsigned char *ptr = (unsigned char *)gs_heap_cursor;
    gs_heap_cursor += sz;
    for (size_t i = 0; i < sz; i++) {
        ptr[i] = 0;
    }
    return (void *)ptr;
}

void *gc_alloc_atomic(int64_t bytes)
{
    return gc_alloc(bytes);
}

void gc_init_with_stack(int64_t heap_words, void *stack_anchor)
{
    (void)heap_words;
    (void)stack_anchor;
    gs_heap_ensure_init();
}

void gc_register_root(void **slot)
{
    if (slot != NULL && gs_root_count < 1024) {
        gs_roots[gs_root_count++] = slot;
    }
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
    unsigned char *d = (unsigned char *)dst;
    const unsigned char *s = (const unsigned char *)src;
    for (int64_t i = 0; i < n; i++) {
        d[i] = s[i];
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
    return gc_alloc((int64_t)bytes);
}

__attribute__((export_name("gs_wasm_str_len")))
int32_t gs_wasm_str_len(const char *s)
{
    return (int32_t)gs_strlen(s);
}

__attribute__((export_name("gs_wasm_heap_used")))
int32_t gs_wasm_heap_used(void)
{
    gs_heap_ensure_init();
    return (int32_t)(gs_heap_cursor - (uintptr_t)&__heap_base);
}
