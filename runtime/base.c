#include "include/gsvalue.h"
#include "include/gc.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

void printLn(const char *s, void *fv)
{
    (void)fv;
    if (s == NULL) {
        puts("");
    } else {
        puts(s);
    }
    fflush(stdout);
}

void putChar(const char c, void *fv)
{
    (void)fv;
    putchar((unsigned char)c);
    fflush(stdout);
}

void putNumber(const int32_t n, void *fv)
{
    (void)fv;
    printf("%d", n);
    fflush(stdout);
}

void putFloat(const double f, void *fv)
{
    (void)fv;
    printf("%g", f);
    fflush(stdout);
}

void putF32(const float f, void *fv)
{
    (void)fv;
    printf("%g", (double)f);
    fflush(stdout);
}

int32_t gs_fmt_f64(double f, char *buf, int32_t cap)
{
    if (buf == NULL || cap <= 0) return 0;
    uint64_t bits = 0;
    memcpy(&bits, &f, sizeof(bits));
    const char *special = NULL;
    if ((bits & 0x7FF0000000000000ULL) == 0x7FF0000000000000ULL) {
        if ((bits & 0x000FFFFFFFFFFFFFULL) != 0ULL) {
            special = "NaN";
        } else {
            special = (bits >> 63) ? "-inf" : "inf";
        }
    } else if ((bits & 0x7FFFFFFFFFFFFFFFULL) == 0ULL) {
        special = (bits >> 63) ? "-0.0" : "0.0";
    }
    if (special != NULL) {
        int32_t n = (int32_t)strlen(special);
        if (n > cap) n = cap;
        memcpy(buf, special, (size_t)n);
        return n;
    }

    char tmp[64];
    int n = snprintf(tmp, sizeof(tmp) - 4, "%.15g", f);
    for (int i = 0; i < n; i++) {
        if (tmp[i] == ',') tmp[i] = '.';
    }
    if (n <= 0 || strtod(tmp, NULL) != f) {
        n = snprintf(tmp, sizeof(tmp) - 4, "%.17g", f);
        for (int i = 0; i < n; i++) {
            if (tmp[i] == ',') tmp[i] = '.';
        }
    }
    if (n <= 0) return 0;

    int has_dot_or_exp = 0;
    for (int i = 0; i < n; i++) {
        char c = tmp[i];
        if (c == '.' || c == 'e' || c == 'E') {
            has_dot_or_exp = 1;
            break;
        }
    }
    if (!has_dot_or_exp && (size_t)(n + 2) < sizeof(tmp)) {
        tmp[n++] = '.';
        tmp[n++] = '0';
        tmp[n] = '\0';
    }
    int32_t out_n = (n > cap) ? cap : (int32_t)n;
    memcpy(buf, tmp, (size_t)out_n);
    return out_n;
}

int32_t gs_str_cmp(const char *a, const char *b)
{
    if (a == b) return 0;
    if (a == NULL) return -1;
    if (b == NULL) return 1;
    int r = strcmp(a, b);
    return (r < 0) ? -1 : (r > 0 ? 1 : 0);
}

void gs_match_fail(void)
{
    fprintf(stderr, "Runtime error: non-exhaustive pattern match failed\n");
    abort();
}

void gs_bounds_fail(int32_t idx, int32_t len)
{
    fprintf(stderr, "Runtime error: array index %d out of bounds (length %d)\n", idx, len);
    abort();
}

void gs_div_zero_fail(void)
{
    fprintf(stderr, "Runtime error: integer division or remainder by zero\n");
    abort();
}
