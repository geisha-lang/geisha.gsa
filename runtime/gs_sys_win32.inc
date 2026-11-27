/* Windows (Win32 + Winsock2 + BCrypt) implementation of `runtime/gs_sys.c` */

#ifndef WIN32_LEAN_AND_MEAN
#define WIN32_LEAN_AND_MEAN
#endif
#include <winsock2.h>
#include <ws2tcpip.h>
#include <windows.h>
#include <aclapi.h>
#include <bcrypt.h>
#include <fcntl.h>
#include <io.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <wchar.h>

#if defined(_MSC_VER) || defined(__clang__)
#pragma comment(lib, "ws2_32.lib")
#pragma comment(lib, "bcrypt.lib")
#pragma comment(lib, "advapi32.lib")
#endif

int64_t gs_sys_rand_seed(void);
int64_t gs_sys_time_mono_ns(void);
int32_t gs_pipe_close(int32_t fd);

/* ---- UTF-8 <-> UTF-16 helpers ---- */

static wchar_t *gs_utf8_to_wide(const char *s)
{
    if (s == NULL) return NULL;
    int need = MultiByteToWideChar(CP_UTF8, 0, s, -1, NULL, 0);
    if (need <= 0) return NULL;
    wchar_t *w = (wchar_t *)malloc((size_t)need * sizeof(wchar_t));
    if (w == NULL) return NULL;
    if (MultiByteToWideChar(CP_UTF8, 0, s, -1, w, need) <= 0) {
        free(w);
        return NULL;
    }
    return w;
}

static char *gs_wide_to_utf8_alloc(const wchar_t *w)
{
    if (w == NULL) return NULL;
    int need = WideCharToMultiByte(CP_UTF8, 0, w, -1, NULL, 0, NULL, NULL);
    if (need <= 0) return NULL;
    char *s = (char *)malloc((size_t)need);
    if (s == NULL) return NULL;
    if (WideCharToMultiByte(CP_UTF8, 0, w, -1, s, need, NULL, NULL) <= 0) {
        free(s);
        return NULL;
    }
    return s;
}

typedef struct {
    wchar_t *buf;
    size_t len;
    size_t cap;
} gs_wbuf_t;

static int gs_wbuf_push(gs_wbuf_t *b, wchar_t ch)
{
    if (b->len + 1u >= b->cap) {
        size_t ncap = (b->cap == 0) ? 256u : (b->cap * 2u);
        wchar_t *nb = (wchar_t *)realloc(b->buf, ncap * sizeof(wchar_t));
        if (nb == NULL) return -1;
        b->buf = nb;
        b->cap = ncap;
    }
    b->buf[b->len++] = ch;
    b->buf[b->len] = L'\0';
    return 0;
}

/* ---- Generational handle token helpers (31-bit non-negative token) ----
 * Lower 14 bits: slot index (0..16383)
 * Upper 17 bits: generation (1..131071, never 0 so dynamic tokens >= 16384)
 */
#define GS_HANDLE_IDX_BITS 14
#define GS_HANDLE_IDX_MASK ((1u << GS_HANDLE_IDX_BITS) - 1u)
#define GS_HANDLE_GEN_MASK 0x1FFFFu

static inline int32_t gs_handle_make(uint32_t idx, uint32_t gen)
{
    return (int32_t)(((gen & GS_HANDLE_GEN_MASK) << GS_HANDLE_IDX_BITS) | (idx & GS_HANDLE_IDX_MASK));
}

static inline uint32_t gs_handle_idx(int32_t tok)
{
    return ((uint32_t)tok) & GS_HANDLE_IDX_MASK;
}

static inline uint32_t gs_handle_gen(int32_t tok)
{
    return (((uint32_t)tok) >> GS_HANDLE_IDX_BITS) & GS_HANDLE_GEN_MASK;
}

static inline uint32_t gs_handle_next_gen(uint32_t g)
{
    return (g >= GS_HANDLE_GEN_MASK) ? 1u : (g + 1u);
}

/* ---- UTF-8 argv & getenv (`sys.env`) ---- */

/* Parse Windows UTF-16 command line using standard CommandLineToArgvW rules (no shell32 dependency) */
void gs_sys_normalize_args(int32_t *argc_ptr, char ***argv_ptr)
{
    if (argc_ptr == NULL || argv_ptr == NULL) return;
    const wchar_t *cmd = GetCommandLineW();
    if (cmd == NULL || *cmd == L'\0') return;

    char **argv = NULL;
    int32_t argc = 0;
    int32_t cap = 0;

    const wchar_t *p = cmd;
    /* argv[0]: program name (quotes toggle without backslash escaping) */
    {
        gs_wbuf_t cur = {NULL, 0, 0};
        int in_q = 0;
        while (*p == L' ' || *p == L'\t') p++;
        while (*p != L'\0' && (in_q || (*p != L' ' && *p != L'\t'))) {
            if (*p == L'"') {
                in_q = !in_q;
            } else if (gs_wbuf_push(&cur, *p) != 0) {
                free(cur.buf);
                return;
            }
            p++;
        }
        char *u8 = gs_wide_to_utf8_alloc(cur.buf ? cur.buf : L"");
        free(cur.buf);
        if (u8 == NULL) return;
        cap = 16;
        argv = (char **)malloc((size_t)(cap + 1) * sizeof(char *));
        if (argv == NULL) {
            free(u8);
            return;
        }
        argv[argc++] = u8;
    }

    while (*p != L'\0') {
        while (*p == L' ' || *p == L'\t') p++;
        if (*p == L'\0') break;
        gs_wbuf_t cur = {NULL, 0, 0};
        int in_q = 0;
        while (*p != L'\0') {
            if (!in_q && (*p == L' ' || *p == L'\t')) break;
            if (*p == L'\\') {
                size_t bs = 0;
                while (*p == L'\\') { bs++; p++; }
                if (*p == L'"') {
                    for (size_t k = 0; k < bs / 2u; k++) {
                        if (gs_wbuf_push(&cur, L'\\') != 0) { free(cur.buf); goto fail_argv; }
                    }
                    if ((bs & 1u) != 0) {
                        if (gs_wbuf_push(&cur, L'"') != 0) { free(cur.buf); goto fail_argv; }
                        p++;
                    } else {
                        in_q = !in_q;
                        p++;
                    }
                } else {
                    for (size_t k = 0; k < bs; k++) {
                        if (gs_wbuf_push(&cur, L'\\') != 0) { free(cur.buf); goto fail_argv; }
                    }
                }
            } else if (*p == L'"') {
                if (in_q && p[1] == L'"') {
                    if (gs_wbuf_push(&cur, L'"') != 0) { free(cur.buf); goto fail_argv; }
                    p += 2;
                } else {
                    in_q = !in_q;
                    p++;
                }
            } else {
                if (gs_wbuf_push(&cur, *p) != 0) { free(cur.buf); goto fail_argv; }
                p++;
            }
        }
        char *u8 = gs_wide_to_utf8_alloc(cur.buf ? cur.buf : L"");
        free(cur.buf);
        if (u8 == NULL) goto fail_argv;
        if (argc >= cap) {
            int32_t ncap = cap * 2;
            char **na = (char **)realloc(argv, (size_t)(ncap + 1) * sizeof(char *));
            if (na == NULL) { free(u8); goto fail_argv; }
            argv = na;
            cap = ncap;
        }
        argv[argc++] = u8;
    }
    argv[argc] = NULL;
    *argc_ptr = argc;
    *argv_ptr = argv;
    return;

fail_argv:
    for (int32_t i = 0; i < argc; i++) free(argv[i]);
    free(argv);
}

static INIT_ONCE _getenv_fls_once = INIT_ONCE_STATIC_INIT;
static DWORD _getenv_fls_key = FLS_OUT_OF_INDEXES;

static void WINAPI gs_getenv_fls_dtor(void *p)
{
    free(p);
}

static BOOL CALLBACK gs_getenv_fls_init_cb(PINIT_ONCE once, PVOID param, PVOID *ctx)
{
    (void)once;
    (void)param;
    (void)ctx;
    _getenv_fls_key = FlsAlloc(gs_getenv_fls_dtor);
    return TRUE;
}

const char *gs_sys_getenv(const char *name)
{
    if (name == NULL || name[0] == '\0') return NULL;
    wchar_t *wname = gs_utf8_to_wide(name);
    if (wname == NULL) return NULL;

    wchar_t *wval = NULL;
    DWORD cap = GetEnvironmentVariableW(wname, NULL, 0);
    if (cap == 0) {
        DWORD err = GetLastError();
        free(wname);
        if (err == ERROR_ENVVAR_NOT_FOUND) return NULL;
        return "";
    }

    int ok = 0;
    for (int attempt = 0; attempt < 16; attempt++) {
        wchar_t *buf = (wchar_t *)malloc((size_t)cap * sizeof(wchar_t));
        if (buf == NULL) {
            free(wname);
            return NULL;
        }
        DWORD got = GetEnvironmentVariableW(wname, buf, cap);
        if (got == 0) {
            DWORD err = GetLastError();
            free(buf);
            free(wname);
            if (err == ERROR_ENVVAR_NOT_FOUND) return NULL;
            return "";
        }
        if (got >= cap) {
            /* Variable grew concurrently between sizing and read: resize and retry */
            free(buf);
            cap = got;
            continue;
        }
        wval = buf;
        ok = 1;
        break;
    }
    free(wname);
    if (!ok || wval == NULL) return NULL;

    char *u8 = gs_wide_to_utf8_alloc(wval);
    free(wval);
    if (u8 == NULL) return NULL;

    InitOnceExecuteOnce(&_getenv_fls_once, gs_getenv_fls_init_cb, NULL, NULL);
    if (_getenv_fls_key == FLS_OUT_OF_INDEXES) {
        free(u8);
        return NULL;
    }
    void *prev = FlsGetValue(_getenv_fls_key);
    if (!FlsSetValue(_getenv_fls_key, u8)) {
        free(u8);
        return NULL;
    }
    free(prev);
    return u8;
}

/* ---- Host platform & executable path discovery (`sys.env`) ---- */

const char *gs_sys_host_os(void)
{
    return "windows";
}

const char *gs_sys_host_arch(void)
{
#if defined(__aarch64__) || defined(_M_ARM64)
    return "arm64";
#elif defined(__x86_64__) || defined(_M_X64)
    return "x86_64";
#else
    return "unknown";
#endif
}

static INIT_ONCE _exe_path_once = INIT_ONCE_STATIC_INIT;
static char _exe_path_buf[4096];

static BOOL CALLBACK gs_init_exe_path_cb(PINIT_ONCE once, PVOID param, PVOID *ctx)
{
    (void)once;
    (void)param;
    (void)ctx;
    wchar_t wbuf[2048];
    DWORD n = GetModuleFileNameW(NULL, wbuf, (DWORD)(sizeof(wbuf) / sizeof(wbuf[0])));
    if (n > 0 && n < (DWORD)(sizeof(wbuf) / sizeof(wbuf[0]))) {
        wbuf[n] = L'\0';
        int ulen = WideCharToMultiByte(
            CP_UTF8, 0, wbuf, -1, _exe_path_buf, (int)sizeof(_exe_path_buf), NULL, NULL);
        if (ulen <= 0) _exe_path_buf[0] = '\0';
    }
    return TRUE;
}

const char *gs_sys_exe_path(void)
{
    InitOnceExecuteOnce(&_exe_path_once, gs_init_exe_path_cb, NULL, NULL);
    return _exe_path_buf[0] != '\0' ? _exe_path_buf : NULL;
}

int32_t gs_sys_getpid(void)
{
    return (int32_t)GetCurrentProcessId();
}

char *gs_sys_realpath(const char *path)
{
    if (path == NULL || path[0] == '\0') return NULL;
    wchar_t *wp = gs_utf8_to_wide(path);
    if (wp == NULL) return NULL;

    /* Prefer GetFinalPathNameByHandleW to resolve directory junctions/symlinks & normalize case/volume */
    HANDLE h = CreateFileW(
        wp, 0, FILE_SHARE_READ | FILE_SHARE_WRITE | FILE_SHARE_DELETE,
        NULL, OPEN_EXISTING, FILE_FLAG_BACKUP_SEMANTICS, NULL);
    if (h != INVALID_HANDLE_VALUE) {
        DWORD need = GetFinalPathNameByHandleW(h, NULL, 0, FILE_NAME_NORMALIZED | VOLUME_NAME_DOS);
        if (need > 0) {
            wchar_t *wfinal = (wchar_t *)malloc(((size_t)need + 1u) * sizeof(wchar_t));
            if (wfinal != NULL) {
                DWORD got = GetFinalPathNameByHandleW(h, wfinal, need, FILE_NAME_NORMALIZED | VOLUME_NAME_DOS);
                CloseHandle(h);
                free(wp);
                if (got > 0 && got < need) {
                    /* Normalize `\\?\UNC\server\share` -> `\\server\share` and `\\?\C:\...` -> `C:\...` */
                    const wchar_t *norm = wfinal;
                    wchar_t *unc_buf = NULL;
                    if (wcsncmp(wfinal, L"\\\\?\\UNC\\", 8) == 0) {
                        size_t rlen = wcslen(wfinal + 8);
                        unc_buf = (wchar_t *)malloc((rlen + 3u) * sizeof(wchar_t));
                        if (unc_buf != NULL) {
                            unc_buf[0] = L'\\';
                            unc_buf[1] = L'\\';
                            memcpy(unc_buf + 2, wfinal + 8, (rlen + 1u) * sizeof(wchar_t));
                            norm = unc_buf;
                        }
                    } else if (wcsncmp(wfinal, L"\\\\?\\", 4) == 0) {
                        norm = wfinal + 4;
                    }
                    char *utf8 = gs_wide_to_utf8_alloc(norm);
                    free(unc_buf);
                    free(wfinal);
                    return utf8;
                }
                free(wfinal);
                return NULL;
            }
        }
        CloseHandle(h);
    }

    /* Fallback if entry exists but handle could not be opened */
    DWORD attrs = GetFileAttributesW(wp);
    if (attrs == INVALID_FILE_ATTRIBUTES) {
        free(wp);
        return NULL;
    }
    DWORD need = GetFullPathNameW(wp, 0, NULL, NULL);
    if (need == 0) {
        free(wp);
        return NULL;
    }
    wchar_t *wfull = (wchar_t *)malloc(((size_t)need + 1u) * sizeof(wchar_t));
    if (wfull == NULL) {
        free(wp);
        return NULL;
    }
    DWORD got = GetFullPathNameW(wp, need, wfull, NULL);
    free(wp);
    if (got == 0) {
        free(wfull);
        return NULL;
    }
    char *utf8 = gs_wide_to_utf8_alloc(wfull);
    free(wfull);
    return utf8;
}

int64_t gs_sys_fd_write(int32_t fd, const void *buf, int64_t len)
{
    if (fd < 0 || buf == NULL || len <= 0) return 0;
    HANDLE h = INVALID_HANDLE_VALUE;
    if (fd == 1) h = GetStdHandle(STD_OUTPUT_HANDLE);
    else if (fd == 2) h = GetStdHandle(STD_ERROR_HANDLE);
    else if (fd < 2048) {
        intptr_t osfh = _get_osfhandle(fd);
        if (osfh != -1 && osfh != -2) h = (HANDLE)osfh;
    }
    if (h == INVALID_HANDLE_VALUE || h == NULL) return -1;

    const unsigned char *p = (const unsigned char *)buf;
    int64_t rem = len;
    while (rem > 0) {
        DWORD chunk = (rem > (int64_t)0x40000000LL) ? (DWORD)0x40000000UL : (DWORD)rem;
        DWORD written = 0;
        if (!WriteFile(h, p, chunk, &written, NULL)) return -1;
        if (written == 0) return -1;
        p += written;
        rem -= (int64_t)written;
    }
    return len;
}

/* ---- Filesystem helpers (`sys.fs`) ---- */

void *gs_sys_fopen(const char *path, const char *mode)
{
    if (path == NULL || mode == NULL) return NULL;
    wchar_t *wp = gs_utf8_to_wide(path);
    wchar_t *wm = gs_utf8_to_wide(mode);
    if (wp == NULL || wm == NULL) {
        free(wp);
        free(wm);
        return NULL;
    }
    FILE *fp = _wfopen(wp, wm);
    free(wp);
    free(wm);
    return (void *)fp;
}

int32_t gs_sys_remove(const char *path)
{
    if (path == NULL || path[0] == '\0') return -1;
    wchar_t *wp = gs_utf8_to_wide(path);
    if (wp == NULL) return -1;
    BOOL ok = DeleteFileW(wp);
    if (!ok && GetLastError() == ERROR_ACCESS_DENIED) {
        DWORD attrs = GetFileAttributesW(wp);
        if (attrs != INVALID_FILE_ATTRIBUTES && (attrs & FILE_ATTRIBUTE_READONLY)) {
            if (SetFileAttributesW(wp, attrs & ~FILE_ATTRIBUTE_READONLY)) {
                ok = DeleteFileW(wp);
                if (!ok) {
                    DWORD del_err = GetLastError();
                    (void)SetFileAttributesW(wp, attrs);
                    SetLastError(del_err);
                }
            }
        }
    }
    free(wp);
    return ok ? 0 : -1;
}

int32_t gs_sys_file_exists(const char *path)
{
    if (path == NULL || path[0] == '\0') return 0;
    wchar_t *wp = gs_utf8_to_wide(path);
    if (wp == NULL) return 0;
    DWORD attrs = GetFileAttributesW(wp);
    free(wp);
    return (attrs != INVALID_FILE_ATTRIBUTES) ? 1 : 0;
}

int32_t gs_sys_rmdir(const char *path)
{
    if (path == NULL || path[0] == '\0') return -1;
    wchar_t *wp = gs_utf8_to_wide(path);
    if (wp == NULL) return -1;
    BOOL ok = RemoveDirectoryW(wp);
    free(wp);
    return ok ? 0 : -1;
}

/* Non-following entry classification:
 *   0 = does not exist
 *  -1 = error
 *   1 = regular file
 *   2 = real directory (not a reparse point)
 *   3 = file symlink / non-dir reparse point
 *   4 = directory symlink / junction (remove via RemoveDirectoryW, never recurse)
 */
int32_t gs_sys_lstat_kind(const char *path)
{
    if (path == NULL || path[0] == '\0') return -1;
    wchar_t *wp = gs_utf8_to_wide(path);
    if (wp == NULL) return -1;
    size_t wlen = wcslen(wp);
    while (wlen > 1u && (wp[wlen - 1u] == L'/' || wp[wlen - 1u] == L'\\')) {
        if (wlen == 3u && wp[1] == L':') break;
        wp[--wlen] = L'\0';
    }
    DWORD attrs = GetFileAttributesW(wp);
    free(wp);
    if (attrs == INVALID_FILE_ATTRIBUTES) {
        DWORD err = GetLastError();
        if (err == ERROR_FILE_NOT_FOUND || err == ERROR_PATH_NOT_FOUND) return 0;
        return -1;
    }
    if (attrs & FILE_ATTRIBUTE_REPARSE_POINT) {
        return (attrs & FILE_ATTRIBUTE_DIRECTORY) ? 4 : 3;
    }
    if (attrs & FILE_ATTRIBUTE_DIRECTORY) return 2;
    return 1;
}

int32_t gs_sys_is_dir(const char *path)
{
    if (path == NULL || path[0] == '\0') return 0;
    wchar_t *wp = gs_utf8_to_wide(path);
    if (wp == NULL) return 0;
    DWORD attrs = GetFileAttributesW(wp);
    free(wp);
    if (attrs == INVALID_FILE_ATTRIBUTES) return 0;
    return (attrs & FILE_ATTRIBUTE_DIRECTORY) ? 1 : 0;
}

int32_t gs_sys_is_symlink(const char *path)
{
    int32_t k = gs_sys_lstat_kind(path);
    return (k == 3 || k == 4) ? 1 : 0;
}

int32_t gs_sys_mkdir(const char *path)
{
    if (path == NULL || path[0] == '\0') return -1;
    wchar_t *wp = gs_utf8_to_wide(path);
    if (wp == NULL) return -1;
    BOOL ok = CreateDirectoryW(wp, NULL);
    DWORD err = ok ? 0 : GetLastError();
    free(wp);
    if (ok) return 0;
    if (err == ERROR_ALREADY_EXISTS) {
        return gs_sys_is_dir(path) ? 0 : -1;
    }
    return -1;
}

typedef struct {
    HANDLE hFind;
    WIN32_FIND_DATAW ffd;
    int has_first;
    char name_utf8[1040];
} gs_win_dir_t;

void *gs_sys_dir_open(const char *path)
{
    if (path == NULL || path[0] == '\0') return NULL;
    size_t len = strlen(path);
    char *pat = (char *)malloc(len + 4u);
    if (pat == NULL) return NULL;
    memcpy(pat, path, len);
    if (len > 0 && (path[len - 1] == '/' || path[len - 1] == '\\')) {
        pat[len] = '*';
        pat[len + 1] = '\0';
    } else {
        pat[len] = '\\';
        pat[len + 1] = '*';
        pat[len + 2] = '\0';
    }
    wchar_t *wpat = gs_utf8_to_wide(pat);
    free(pat);
    if (wpat == NULL) return NULL;

    gs_win_dir_t *d = (gs_win_dir_t *)calloc(1, sizeof(gs_win_dir_t));
    if (d == NULL) {
        free(wpat);
        return NULL;
    }
    d->hFind = FindFirstFileW(wpat, &d->ffd);
    free(wpat);
    if (d->hFind == INVALID_HANDLE_VALUE) {
        free(d);
        return NULL;
    }
    d->has_first = 1;
    return (void *)d;
}

const char *gs_sys_dir_next(void *dir)
{
    if (dir == NULL) return NULL;
    gs_win_dir_t *d = (gs_win_dir_t *)dir;
    for (;;) {
        if (d->has_first) {
            d->has_first = 0;
        } else {
            if (!FindNextFileW(d->hFind, &d->ffd)) return NULL;
        }
        if (wcscmp(d->ffd.cFileName, L".") == 0 || wcscmp(d->ffd.cFileName, L"..") == 0) {
            continue;
        }
        int n = WideCharToMultiByte(
            CP_UTF8, 0, d->ffd.cFileName, -1, d->name_utf8, (int)sizeof(d->name_utf8), NULL, NULL);
        if (n <= 0) continue;
        return d->name_utf8;
    }
}

int32_t gs_sys_dir_close(void *dir)
{
    if (dir == NULL) return 0;
    gs_win_dir_t *d = (gs_win_dir_t *)dir;
    if (d->hFind != INVALID_HANDLE_VALUE) {
        FindClose(d->hFind);
    }
    free(d);
    return 0;
}

int64_t gs_sys_file_size(const char *path)
{
    if (path == NULL || path[0] == '\0') return -1;
    wchar_t *wp = gs_utf8_to_wide(path);
    if (wp == NULL) return -1;
    WIN32_FILE_ATTRIBUTE_DATA fad;
    BOOL ok = GetFileAttributesExW(wp, GetFileExInfoStandard, &fad);
    free(wp);
    if (!ok || (fad.dwFileAttributes & FILE_ATTRIBUTE_DIRECTORY)) return -1;
    return (int64_t)(((uint64_t)fad.nFileSizeHigh << 32) | (uint64_t)fad.nFileSizeLow);
}

void *gs_sys_mmap_open(const char *path)
{
    if (path == NULL || path[0] == '\0') return NULL;
    wchar_t *wp = gs_utf8_to_wide(path);
    if (wp == NULL) return NULL;
    HANDLE hFile = CreateFileW(
        wp, GENERIC_READ, FILE_SHARE_READ | FILE_SHARE_WRITE | FILE_SHARE_DELETE,
        NULL, OPEN_EXISTING, FILE_ATTRIBUTE_NORMAL, NULL);
    free(wp);
    if (hFile == INVALID_HANDLE_VALUE) return NULL;

    LARGE_INTEGER sz;
    if (!GetFileSizeEx(hFile, &sz) || sz.QuadPart <= 0) {
        CloseHandle(hFile);
        return NULL;
    }
    HANDLE hMap = CreateFileMappingW(hFile, NULL, PAGE_READONLY, 0, 0, NULL);
    CloseHandle(hFile);
    if (hMap == NULL) return NULL;

    void *view = MapViewOfFile(hMap, FILE_MAP_READ, 0, 0, 0);
    CloseHandle(hMap);
    return view;
}

int32_t gs_sys_mmap_close(void *ptr, int64_t len)
{
    (void)len;
    if (ptr == NULL) return 0;
    return UnmapViewOfFile(ptr) ? 0 : -1;
}

int32_t gs_sys_write_atomic(const char *path, const void *buf, int64_t len, int32_t mode)
{
    if (path == NULL || path[0] == '\0' || len < 0 || (len > 0 && buf == NULL)) {
        return -1;
    }
    size_t plen = strlen(path);
    char *tmp_path = (char *)malloc(plen + 40u);
    if (tmp_path == NULL) return -1;

    const char *slash_f = strrchr(path, '/');
    const char *slash_b = strrchr(path, '\\');
    const char *slash = (slash_b != NULL && (slash_f == NULL || slash_b > slash_f)) ? slash_b : slash_f;

    HANDLE hFile = INVALID_HANDLE_VALUE;
    wchar_t *wtmp = NULL;
    uint64_t rng = (uint64_t)gs_sys_rand_seed();
    for (int attempt = 0; attempt < 32; attempt++) {
        rng = rng * 6364136223846793005ULL + 1442695040888963407ULL + (uint64_t)attempt;
        unsigned long long tag = (unsigned long long)rng;
        if (slash == NULL) {
            snprintf(tmp_path, plen + 40u, ".%s.tmp.%016llx", path, tag);
        } else {
            size_t dlen = (size_t)(slash - path) + 1u;
            memcpy(tmp_path, path, dlen);
            snprintf(tmp_path + dlen, plen + 40u - dlen, ".%s.tmp.%016llx", slash + 1, tag);
        }
        wtmp = gs_utf8_to_wide(tmp_path);
        if (wtmp == NULL) {
            free(tmp_path);
            return -1;
        }
        hFile = CreateFileW(
            wtmp, GENERIC_WRITE, 0, NULL, CREATE_NEW, FILE_ATTRIBUTE_NORMAL, NULL);
        if (hFile != INVALID_HANDLE_VALUE) break;
        DWORD err = GetLastError();
        free(wtmp);
        wtmp = NULL;
        if (err != ERROR_FILE_EXISTS) {
            free(tmp_path);
            return -1;
        }
    }
    free(tmp_path);
    if (hFile == INVALID_HANDLE_VALUE || wtmp == NULL) {
        free(wtmp);
        return -1;
    }

    const unsigned char *p = (const unsigned char *)buf;
    int64_t rem = len;
    while (rem > 0) {
        DWORD chunk = (rem > (int64_t)0x40000000LL) ? (DWORD)0x40000000UL : (DWORD)rem;
        DWORD written = 0;
        if (!WriteFile(hFile, p, chunk, &written, NULL) || written == 0) {
            CloseHandle(hFile);
            DeleteFileW(wtmp);
            free(wtmp);
            return -1;
        }
        p += written;
        rem -= (int64_t)written;
    }

    if (!FlushFileBuffers(hFile)) {
        CloseHandle(hFile);
        DeleteFileW(wtmp);
        free(wtmp);
        return -1;
    }
    if (!CloseHandle(hFile)) {
        DeleteFileW(wtmp);
        free(wtmp);
        return -1;
    }

    if (mode >= 0 && (mode & 0222) == 0) {
        (void)_wchmod(wtmp, _S_IREAD);
    }

    wchar_t *wdst = gs_utf8_to_wide(path);
    if (wdst == NULL) {
        DeleteFileW(wtmp);
        free(wtmp);
        return -1;
    }
    BOOL moved = MoveFileExW(wtmp, wdst, MOVEFILE_REPLACE_EXISTING | MOVEFILE_WRITE_THROUGH);
    free(wdst);
    if (!moved) {
        DeleteFileW(wtmp);
        free(wtmp);
        return -1;
    }
    free(wtmp);
    return 0;
}

int32_t gs_sys_rename(const char *src, const char *dst)
{
    if (src == NULL || dst == NULL) return -1;
    wchar_t *wsrc = gs_utf8_to_wide(src);
    wchar_t *wdst = gs_utf8_to_wide(dst);
    if (wsrc == NULL || wdst == NULL) {
        free(wsrc);
        free(wdst);
        return -1;
    }
    BOOL ok = MoveFileExW(wsrc, wdst, MOVEFILE_REPLACE_EXISTING);
    free(wsrc);
    free(wdst);
    return ok ? 0 : -1;
}

int32_t gs_sys_chmod(const char *path, int32_t mode)
{
    if (path == NULL || mode < 0) return -1;
    wchar_t *wp = gs_utf8_to_wide(path);
    if (wp == NULL) return -1;
    int pmode = (mode & 0222) ? (_S_IREAD | _S_IWRITE) : _S_IREAD;
    int rc = _wchmod(wp, pmode);
    free(wp);
    return (rc == 0) ? 0 : -1;
}

int32_t gs_sys_file_mode(const char *path)
{
    (void)path;
    return -1;
}

int32_t gs_sys_write_excl(const char *path, const void *buf, int64_t len, int32_t mode)
{
    (void)mode;
    if (path == NULL || path[0] == '\0' || len < 0 || (len > 0 && buf == NULL)) return -1;
    wchar_t *wp = gs_utf8_to_wide(path);
    if (wp == NULL) return -1;

    /* Build a restrictive owner-only protected DACL so the staged file is never
     * readable by other users between CreateFileW and gs_sys_copy_file_acl. */
    HANDLE tok = NULL;
    if (!OpenProcessToken(GetCurrentProcess(), TOKEN_QUERY, &tok)) {
        free(wp);
        return -1;
    }
    DWORD need = 0;
    GetTokenInformation(tok, TokenUser, NULL, 0, &need);
    if (need == 0) {
        CloseHandle(tok);
        free(wp);
        return -1;
    }
    TOKEN_USER *tu = (TOKEN_USER *)malloc(need);
    if (tu == NULL || !GetTokenInformation(tok, TokenUser, tu, need, &need)) {
        free(tu);
        CloseHandle(tok);
        free(wp);
        return -1;
    }
    CloseHandle(tok);

    EXPLICIT_ACCESSW ea;
    ZeroMemory(&ea, sizeof(ea));
    ea.grfAccessPermissions = FILE_ALL_ACCESS;
    ea.grfAccessMode = SET_ACCESS;
    ea.grfInheritance = NO_INHERITANCE;
    ea.Trustee.TrusteeForm = TRUSTEE_IS_SID;
    ea.Trustee.TrusteeType = TRUSTEE_IS_USER;
    ea.Trustee.ptstrName = (LPWCH)tu->User.Sid;

    PACL ownerDacl = NULL;
    if (SetEntriesInAclW(1, &ea, NULL, &ownerDacl) != ERROR_SUCCESS || ownerDacl == NULL) {
        free(tu);
        free(wp);
        return -1;
    }
    SECURITY_DESCRIPTOR sd;
    if (!InitializeSecurityDescriptor(&sd, SECURITY_DESCRIPTOR_REVISION) ||
        !SetSecurityDescriptorDacl(&sd, TRUE, ownerDacl, FALSE) ||
        !SetSecurityDescriptorControl(&sd, SE_DACL_PROTECTED, SE_DACL_PROTECTED)) {
        LocalFree(ownerDacl);
        free(tu);
        free(wp);
        return -1;
    }
    SECURITY_ATTRIBUTES sa;
    sa.nLength = sizeof(sa);
    sa.lpSecurityDescriptor = &sd;
    sa.bInheritHandle = FALSE;

    HANDLE h = CreateFileW(wp, GENERIC_WRITE, 0, &sa, CREATE_NEW, FILE_ATTRIBUTE_NORMAL, NULL);
    DWORD createErr = (h == INVALID_HANDLE_VALUE) ? GetLastError() : ERROR_SUCCESS;
    LocalFree(ownerDacl);
    free(tu);
    if (h == INVALID_HANDLE_VALUE) {
        free(wp);
        if (createErr == ERROR_FILE_EXISTS || createErr == ERROR_ALREADY_EXISTS) return 1;
        return -1;
    }
    const uint8_t *p = (const uint8_t *)buf;
    int64_t rem = len;
    int ok = 1;
    while (rem > 0) {
        DWORD chunk = (rem > 0x40000000LL) ? (DWORD)0x40000000U : (DWORD)rem;
        DWORD written = 0;
        if (!WriteFile(h, p, chunk, &written, NULL) || written == 0) {
            ok = 0;
            break;
        }
        p += written;
        rem -= (int64_t)written;
    }
    if (!CloseHandle(h)) ok = 0;
    if (!ok) {
        DeleteFileW(wp);
        free(wp);
        return -1;
    }
    free(wp);
    return 0;
}

int32_t gs_sys_copy_file_acl(const char *src, const char *dst)
{
    if (src == NULL || dst == NULL || src[0] == '\0' || dst[0] == '\0') return -1;
    wchar_t *wsrc = gs_utf8_to_wide(src);
    wchar_t *wdst = gs_utf8_to_wide(dst);
    if (wsrc == NULL || wdst == NULL) {
        free(wsrc);
        free(wdst);
        return -1;
    }
    PACL dacl = NULL;
    PSECURITY_DESCRIPTOR sd = NULL;
    DWORD grc = GetNamedSecurityInfoW(wsrc, SE_FILE_OBJECT, DACL_SECURITY_INFORMATION, NULL, NULL, &dacl, NULL, &sd);
    if (grc != ERROR_SUCCESS) {
        free(wsrc);
        free(wdst);
        return -1;
    }
    SECURITY_DESCRIPTOR_CONTROL ctrl = 0;
    DWORD rev = 0;
    SECURITY_INFORMATION secInfo = DACL_SECURITY_INFORMATION;
    if (GetSecurityDescriptorControl(sd, &ctrl, &rev)) {
        if (ctrl & SE_DACL_PROTECTED) secInfo |= PROTECTED_DACL_SECURITY_INFORMATION;
        else secInfo |= UNPROTECTED_DACL_SECURITY_INFORMATION;
    }
    DWORD src_rc = SetNamedSecurityInfoW(wdst, SE_FILE_OBJECT, secInfo, NULL, NULL, dacl, NULL);
    LocalFree(sd);
    DWORD attrs = GetFileAttributesW(wsrc);
    if (src_rc == ERROR_SUCCESS && attrs != INVALID_FILE_ATTRIBUTES && (attrs & FILE_ATTRIBUTE_READONLY)) {
        DWORD dattrs = GetFileAttributesW(wdst);
        if (dattrs != INVALID_FILE_ATTRIBUTES) {
            SetFileAttributesW(wdst, dattrs | FILE_ATTRIBUTE_READONLY);
        }
    }
    free(wsrc);
    free(wdst);
    return (src_rc == ERROR_SUCCESS) ? 0 : -1;
}

/* For a brand-new file staged with an owner-only protected DACL, obtain the exact kernel-computed
 * default DACL (inheritable parent ACEs or fallback to the creator token's default DACL) by
 * creating an empty sibling template with NULL SECURITY_ATTRIBUTES, copying its DACL onto `path`,
 * and deleting the empty template. */
int32_t gs_sys_apply_umask_mode(const char *path, int32_t base_mode)
{
    (void)base_mode;
    if (path == NULL || path[0] == '\0') return -1;
    static volatile LONG gs_win_tmpl_seq = 0;
    const char *s1 = strrchr(path, '\\');
    const char *s2 = strrchr(path, '/');
    const char *sep = (s1 != NULL && (s2 == NULL || s1 > s2)) ? s1 : s2;
    size_t pfx_len = (sep != NULL) ? (size_t)(sep - path + 1) : 0;
    unsigned long pid = (unsigned long)GetCurrentProcessId();
    char *tmpl = (char *)malloc(pfx_len + 64);
    if (tmpl == NULL) return -1;
    if (pfx_len > 0) memcpy(tmpl, path, pfx_len);

    wchar_t *wtmpl = NULL;
    int created = 0;
    for (int attempt = 0; attempt < 10000; attempt++) {
        LONG seq = InterlockedIncrement(&gs_win_tmpl_seq);
        snprintf(tmpl + pfx_len, 64, ".gsp_%lu_%ld", pid, (long)seq);
        wtmpl = gs_utf8_to_wide(tmpl);
        if (wtmpl == NULL) {
            free(tmpl);
            return -1;
        }
        HANDLE h = CreateFileW(wtmpl, GENERIC_WRITE, 0, NULL, CREATE_NEW, FILE_ATTRIBUTE_NORMAL, NULL);
        if (h != INVALID_HANDLE_VALUE) {
            CloseHandle(h);
            created = 1;
            break;
        }
        DWORD err = GetLastError();
        free(wtmpl);
        wtmpl = NULL;
        if (err != ERROR_FILE_EXISTS && err != ERROR_ALREADY_EXISTS) {
            free(tmpl);
            return -1;
        }
    }
    if (!created) {
        free(tmpl);
        return -1;
    }
    int32_t rc = gs_sys_copy_file_acl(tmpl, path);
    DeleteFileW(wtmpl);
    free(wtmpl);
    free(tmpl);
    return rc;
}

static int64_t gs_filetime_to_unix_ms(FILETIME ft)
{
    uint64_t t = ((uint64_t)ft.dwHighDateTime << 32) | (uint64_t)ft.dwLowDateTime;
    const uint64_t EPOCH_DIFF = 116444736000000000ULL;
    if (t < EPOCH_DIFF) return 0;
    return (int64_t)((t - EPOCH_DIFF) / 10000ULL);
}

int64_t gs_sys_file_mtime_ms(const char *path)
{
    if (path == NULL || path[0] == '\0') return -1;
    wchar_t *wp = gs_utf8_to_wide(path);
    if (wp == NULL) return -1;
    WIN32_FILE_ATTRIBUTE_DATA fad;
    BOOL ok = GetFileAttributesExW(wp, GetFileExInfoStandard, &fad);
    free(wp);
    if (!ok) return -1;
    return gs_filetime_to_unix_ms(fad.ftLastWriteTime);
}

/* ---- Time helpers (`sys.time`) ---- */

int64_t gs_sys_time_now_ms(void)
{
    FILETIME ft;
    GetSystemTimeAsFileTime(&ft);
    return gs_filetime_to_unix_ms(ft);
}

static INIT_ONCE _qpc_once = INIT_ONCE_STATIC_INIT;
static LARGE_INTEGER _qpc_freq = {0};

static BOOL CALLBACK gs_init_qpc_cb(PINIT_ONCE once, PVOID param, PVOID *ctx)
{
    (void)once;
    (void)param;
    (void)ctx;
    QueryPerformanceFrequency(&_qpc_freq);
    return TRUE;
}

int64_t gs_sys_time_mono_ns(void)
{
    InitOnceExecuteOnce(&_qpc_once, gs_init_qpc_cb, NULL, NULL);
    LARGE_INTEGER now;
    QueryPerformanceCounter(&now);
    int64_t f = _qpc_freq.QuadPart;
    if (f <= 0) return 0;
    int64_t sec = now.QuadPart / f;
    int64_t rem = now.QuadPart % f;
    return sec * 1000000000LL + (rem * 1000000000LL) / f;
}

int64_t gs_sys_time_mono_ms(void)
{
    return gs_sys_time_mono_ns() / 1000000LL;
}

/* ---- Benchmark optimization barriers (`std.bench`) ---- */

void gs_bench_black_box_mem(void *slot)
{
    if (slot == NULL) return;
    __asm__ volatile("" : "+m"(*(volatile uint64_t *)slot) :: "memory");
}

void gs_bench_black_box_void(void)
{
    __asm__ volatile("" ::: "memory");
}

/* ---- OS entropy seed (`std.rand`) ---- */

int64_t gs_sys_rand_seed(void)
{
    uint64_t seed = 0;
    if (BCryptGenRandom(NULL, (PUCHAR)&seed, (ULONG)sizeof(seed), BCRYPT_USE_SYSTEM_PREFERRED_RNG) != 0) {
        seed = (uint64_t)gs_sys_time_mono_ns() ^ ((uint64_t)GetCurrentProcessId() << 32);
    }
    return (int64_t)seed;
}

/* ---- Winsock2 TCP socket helpers (`sys.net`) with generational refcounted table ---- */

typedef struct {
    SOCKET sock;
    WSAEVENT close_ev;
    WSAEVENT accept_ev;
    uint32_t gen;
    uint32_t refs;
    int in_use;
    int closing;
} gs_win_sock_slot_t;

static INIT_ONCE _wsa_once = INIT_ONCE_STATIC_INIT;
static SRWLOCK _sock_mu = SRWLOCK_INIT;
static gs_win_sock_slot_t *_sock_slots = NULL;
static uint32_t _sock_cap = 0;

static BOOL CALLBACK gs_wsa_init_cb(PINIT_ONCE once, PVOID param, PVOID *ctx)
{
    (void)once;
    (void)param;
    (void)ctx;
    WSADATA wsa;
    (void)WSAStartup(MAKEWORD(2, 2), &wsa);
    return TRUE;
}

static void gs_ensure_wsa(void)
{
    InitOnceExecuteOnce(&_wsa_once, gs_wsa_init_cb, NULL, NULL);
}

static int32_t gs_sock_alloc_fd_ex(SOCKET s, WSAEVENT close_ev, WSAEVENT accept_ev)
{
    AcquireSRWLockExclusive(&_sock_mu);
    for (uint32_t i = 0; i < _sock_cap; i++) {
        if (!_sock_slots[i].in_use) {
            if (_sock_slots[i].gen == 0) _sock_slots[i].gen = 1u;
            _sock_slots[i].sock = s;
            _sock_slots[i].close_ev = close_ev;
            _sock_slots[i].accept_ev = accept_ev;
            _sock_slots[i].refs = 1u;
            _sock_slots[i].in_use = 1;
            _sock_slots[i].closing = 0;
            int32_t tok = gs_handle_make(i, _sock_slots[i].gen);
            ReleaseSRWLockExclusive(&_sock_mu);
            return tok;
        }
    }
    if (_sock_cap >= (1u << GS_HANDLE_IDX_BITS)) {
        ReleaseSRWLockExclusive(&_sock_mu);
        return -1;
    }
    uint32_t new_cap = (_sock_cap == 0) ? 64u : (_sock_cap * 2u);
    if (new_cap > (1u << GS_HANDLE_IDX_BITS)) new_cap = (1u << GS_HANDLE_IDX_BITS);
    gs_win_sock_slot_t *ns = (gs_win_sock_slot_t *)realloc(
        _sock_slots, (size_t)new_cap * sizeof(gs_win_sock_slot_t));
    if (ns == NULL) {
        ReleaseSRWLockExclusive(&_sock_mu);
        return -1;
    }
    for (uint32_t i = _sock_cap; i < new_cap; i++) {
        ns[i].sock = INVALID_SOCKET;
        ns[i].close_ev = WSA_INVALID_EVENT;
        ns[i].accept_ev = WSA_INVALID_EVENT;
        ns[i].gen = 1u;
        ns[i].refs = 0u;
        ns[i].in_use = 0;
        ns[i].closing = 0;
    }
    uint32_t idx = _sock_cap;
    ns[idx].sock = s;
    ns[idx].close_ev = close_ev;
    ns[idx].accept_ev = accept_ev;
    ns[idx].refs = 1u;
    ns[idx].in_use = 1;
    ns[idx].closing = 0;
    _sock_slots = ns;
    _sock_cap = new_cap;
    int32_t tok = gs_handle_make(idx, ns[idx].gen);
    ReleaseSRWLockExclusive(&_sock_mu);
    return tok;
}

static int32_t gs_sock_alloc_fd(SOCKET s)
{
    return gs_sock_alloc_fd_ex(s, WSA_INVALID_EVENT, WSA_INVALID_EVENT);
}

static SOCKET gs_sock_acquire_ex(int32_t tok, WSAEVENT *out_close_ev, WSAEVENT *out_accept_ev)
{
    if (out_close_ev != NULL) *out_close_ev = WSA_INVALID_EVENT;
    if (out_accept_ev != NULL) *out_accept_ev = WSA_INVALID_EVENT;
    if (tok < 0) return INVALID_SOCKET;
    uint32_t idx = gs_handle_idx(tok);
    uint32_t gen = gs_handle_gen(tok);
    if (gen == 0) return INVALID_SOCKET;
    AcquireSRWLockExclusive(&_sock_mu);
    SOCKET s = INVALID_SOCKET;
    if (idx < _sock_cap && _sock_slots[idx].in_use && !_sock_slots[idx].closing && _sock_slots[idx].gen == gen) {
        _sock_slots[idx].refs++;
        s = _sock_slots[idx].sock;
        if (out_close_ev != NULL) *out_close_ev = _sock_slots[idx].close_ev;
        if (out_accept_ev != NULL) *out_accept_ev = _sock_slots[idx].accept_ev;
    }
    ReleaseSRWLockExclusive(&_sock_mu);
    return s;
}

static SOCKET gs_sock_acquire(int32_t tok)
{
    return gs_sock_acquire_ex(tok, NULL, NULL);
}

static int32_t gs_sock_release(int32_t tok)
{
    uint32_t idx = gs_handle_idx(tok);
    SOCKET to_close = INVALID_SOCKET;
    WSAEVENT ev_close = WSA_INVALID_EVENT;
    WSAEVENT ev_accept = WSA_INVALID_EVENT;
    AcquireSRWLockExclusive(&_sock_mu);
    if (idx < _sock_cap && _sock_slots[idx].in_use && _sock_slots[idx].refs > 0) {
        _sock_slots[idx].refs--;
        if (_sock_slots[idx].refs == 0 && _sock_slots[idx].closing) {
            to_close = _sock_slots[idx].sock;
            ev_close = _sock_slots[idx].close_ev;
            ev_accept = _sock_slots[idx].accept_ev;
            _sock_slots[idx].sock = INVALID_SOCKET;
            _sock_slots[idx].close_ev = WSA_INVALID_EVENT;
            _sock_slots[idx].accept_ev = WSA_INVALID_EVENT;
            _sock_slots[idx].in_use = 0;
            _sock_slots[idx].closing = 0;
            _sock_slots[idx].gen = gs_handle_next_gen(_sock_slots[idx].gen);
        }
    }
    ReleaseSRWLockExclusive(&_sock_mu);
    if (to_close != INVALID_SOCKET) {
        (void)WSAEventSelect(to_close, NULL, 0);
    }
    if (ev_accept != WSA_INVALID_EVENT && ev_accept != NULL) {
        (void)WSACloseEvent(ev_accept);
    }
    if (ev_close != WSA_INVALID_EVENT && ev_close != NULL) {
        (void)WSACloseEvent(ev_close);
    }
    if (to_close != INVALID_SOCKET) {
        return (closesocket(to_close) == 0) ? 0 : -1;
    }
    return 0;
}

static void gs_configure_socket(SOCKET s)
{
    (void)SetHandleInformation((HANDLE)s, HANDLE_FLAG_INHERIT, 0);
    int one = 1;
    setsockopt(s, IPPROTO_TCP, TCP_NODELAY, (const char *)&one, (int)sizeof(one));
}

int32_t gs_net_tcp_listen(const char *host, int32_t port, int32_t backlog)
{
    if (port < 0 || port > 65535) return -1;
    gs_ensure_wsa();
    SOCKET s = socket(AF_INET, SOCK_STREAM, IPPROTO_TCP);
    if (s == INVALID_SOCKET) return -1;
    (void)SetHandleInformation((HANDLE)s, HANDLE_FLAG_INHERIT, 0);

    int one = 1;
    setsockopt(s, SOL_SOCKET, SO_REUSEADDR, (const char *)&one, (int)sizeof(one));

    struct sockaddr_in addr;
    memset(&addr, 0, sizeof(addr));
    addr.sin_family = AF_INET;
    addr.sin_port = htons((uint16_t)port);
    if (host == NULL || host[0] == '\0' || strcmp(host, "0.0.0.0") == 0) {
        addr.sin_addr.s_addr = htonl(INADDR_ANY);
    } else if (inet_pton(AF_INET, host, &addr.sin_addr) != 1) {
        closesocket(s);
        return -1;
    }

    if (bind(s, (struct sockaddr *)&addr, (int)sizeof(addr)) != 0) {
        closesocket(s);
        return -1;
    }
    int q = (backlog > 0) ? backlog : 128;
    if (listen(s, q) != 0) {
        closesocket(s);
        return -1;
    }
    WSAEVENT close_ev = WSACreateEvent();
    if (close_ev == WSA_INVALID_EVENT) {
        closesocket(s);
        return -1;
    }
    WSAEVENT accept_ev = WSACreateEvent();
    if (accept_ev == WSA_INVALID_EVENT) {
        (void)WSACloseEvent(close_ev);
        closesocket(s);
        return -1;
    }
    /* Register WSAEventSelect once for the listener lifetime so concurrent accepts never overwrite it */
    if (WSAEventSelect(s, accept_ev, FD_ACCEPT | FD_CLOSE) != 0) {
        (void)WSACloseEvent(accept_ev);
        (void)WSACloseEvent(close_ev);
        closesocket(s);
        return -1;
    }
    int32_t fd = gs_sock_alloc_fd_ex(s, close_ev, accept_ev);
    if (fd < 0) {
        (void)WSAEventSelect(s, NULL, 0);
        (void)WSACloseEvent(accept_ev);
        (void)WSACloseEvent(close_ev);
        closesocket(s);
    }
    return fd;
}

int32_t gs_net_tcp_local_port(int32_t fd)
{
    SOCKET s = gs_sock_acquire(fd);
    if (s == INVALID_SOCKET) return -1;
    struct sockaddr_in addr;
    int len = (int)sizeof(addr);
    memset(&addr, 0, sizeof(addr));
    int rc = getsockname(s, (struct sockaddr *)&addr, &len);
    (void)gs_sock_release(fd);
    if (rc != 0) return -1;
    return (int32_t)ntohs(addr.sin_port);
}

int32_t gs_net_tcp_accept(int32_t listen_fd)
{
    WSAEVENT close_ev = WSA_INVALID_EVENT;
    WSAEVENT accept_ev = WSA_INVALID_EVENT;
    SOCKET ls = gs_sock_acquire_ex(listen_fd, &close_ev, &accept_ev);
    if (ls == INVALID_SOCKET) return -1;
    if (accept_ev == WSA_INVALID_EVENT || accept_ev == NULL) {
        (void)gs_sock_release(listen_fd);
        return -1;
    }

    int32_t res = -1;
    for (;;) {
        if (close_ev != WSA_INVALID_EVENT && close_ev != NULL
            && WaitForSingleObject(close_ev, 0) == WAIT_OBJECT_0) {
            break;
        }
        SOCKET client = accept(ls, NULL, NULL);
        if (client != INVALID_SOCKET) {
            /* Accepted socket inherits listener's WSAEventSelect non-blocking mode; restore blocking */
            (void)WSAEventSelect(client, NULL, 0);
            u_long blocking = 0;
            (void)ioctlsocket(client, FIONBIO, &blocking);
            gs_configure_socket(client);
            res = gs_sock_alloc_fd(client);
            if (res < 0) closesocket(client);
            break;
        }
        int err = WSAGetLastError();
        if (err == WSAEINTR) continue;
        if (err != WSAEWOULDBLOCK) break;

        /* Only reset accept_ev after accept() observed WSAEWOULDBLOCK so queued peers are never swallowed */
        WSANETWORKEVENTS net_ev;
        memset(&net_ev, 0, sizeof(net_ev));
        if (WSAEnumNetworkEvents(ls, accept_ev, &net_ev) == 0) {
            if (net_ev.lNetworkEvents & FD_ACCEPT) continue;
            if (net_ev.lNetworkEvents & FD_CLOSE) break;
        }

        WSAEVENT evs[2];
        DWORD nev = 0;
        if (close_ev != WSA_INVALID_EVENT && close_ev != NULL) {
            evs[nev++] = close_ev;
        }
        DWORD acc_idx = nev;
        evs[nev++] = accept_ev;
        DWORD w = WSAWaitForMultipleEvents(nev, evs, FALSE, WSA_INFINITE, FALSE);
        if (w == WSA_WAIT_EVENT_0 + acc_idx) {
            continue;
        }
        /* close_ev signaled or wait failed: abort accept */
        break;
    }

    (void)gs_sock_release(listen_fd);
    return res;
}

int32_t gs_net_tcp_connect(const char *host, int32_t port)
{
    if (host == NULL || port <= 0 || port > 65535) return -1;
    gs_ensure_wsa();
    char port_str[16];
    snprintf(port_str, sizeof(port_str), "%d", port);

    struct addrinfo hints;
    memset(&hints, 0, sizeof(hints));
    hints.ai_family = AF_INET;
    hints.ai_socktype = SOCK_STREAM;

    struct addrinfo *res = NULL;
    if (getaddrinfo(host, port_str, &hints, &res) != 0 || res == NULL) {
        return -1;
    }

    SOCKET connected = INVALID_SOCKET;
    for (struct addrinfo *p = res; p != NULL; p = p->ai_next) {
        SOCKET cand = socket(p->ai_family, p->ai_socktype, p->ai_protocol);
        if (cand == INVALID_SOCKET) continue;
        (void)SetHandleInformation((HANDLE)cand, HANDLE_FLAG_INHERIT, 0);
        if (connect(cand, p->ai_addr, (int)p->ai_addrlen) == 0) {
            gs_configure_socket(cand);
            connected = cand;
            break;
        }
        closesocket(cand);
    }
    freeaddrinfo(res);
    if (connected == INVALID_SOCKET) return -1;
    int32_t fd = gs_sock_alloc_fd(connected);
    if (fd < 0) closesocket(connected);
    return fd;
}

int32_t gs_net_tcp_read(int32_t fd, void *buf, int32_t cap)
{
    if (buf == NULL || cap <= 0) return 0;
    SOCKET s = gs_sock_acquire(fd);
    if (s == INVALID_SOCKET) return -1;
    int32_t out = -1;
    for (;;) {
        int n = recv(s, (char *)buf, cap, 0);
        if (n >= 0) { out = (int32_t)n; break; }
        if (WSAGetLastError() == WSAEINTR) continue;
        break;
    }
    gs_sock_release(fd);
    return out;
}

int32_t gs_net_tcp_peek(int32_t fd, void *buf, int32_t cap)
{
    if (buf == NULL || cap <= 0) return 0;
    SOCKET s = gs_sock_acquire(fd);
    if (s == INVALID_SOCKET) return -1;
    int32_t out = -1;
    for (;;) {
        int n = recv(s, (char *)buf, cap, MSG_PEEK);
        if (n >= 0) { out = (int32_t)n; break; }
        if (WSAGetLastError() == WSAEINTR) continue;
        break;
    }
    gs_sock_release(fd);
    return out;
}

int32_t gs_net_tcp_write(int32_t fd, const void *buf, int32_t len)
{
    if (buf == NULL || len <= 0) return 0;
    SOCKET s = gs_sock_acquire(fd);
    if (s == INVALID_SOCKET) return -1;
    int32_t out = -1;
    for (;;) {
        int n = send(s, (const char *)buf, len, 0);
        if (n >= 0) { out = (int32_t)n; break; }
        if (WSAGetLastError() == WSAEINTR) continue;
        break;
    }
    gs_sock_release(fd);
    return out;
}

int32_t gs_net_tcp_close(int32_t fd)
{
    if (fd < 0) return 0;
    uint32_t idx = gs_handle_idx(fd);
    uint32_t gen = gs_handle_gen(fd);
    if (gen == 0) return 0;
    SOCKET to_cancel = INVALID_SOCKET;
    WSAEVENT to_wake = WSA_INVALID_EVENT;
    int owned = 0;
    AcquireSRWLockExclusive(&_sock_mu);
    if (idx < _sock_cap && _sock_slots[idx].in_use && !_sock_slots[idx].closing && _sock_slots[idx].gen == gen) {
        _sock_slots[idx].closing = 1;
        /* Retain the owner ref across shutdown/WSASetEvent so no concurrent release can closesocket early */
        to_cancel = _sock_slots[idx].sock;
        to_wake = _sock_slots[idx].close_ev;
        owned = 1;
    }
    ReleaseSRWLockExclusive(&_sock_mu);
    if (!owned) return 0;
    if (to_cancel != INVALID_SOCKET) {
        (void)shutdown(to_cancel, SD_BOTH);
    }
    if (to_wake != WSA_INVALID_EVENT && to_wake != NULL) {
        (void)WSASetEvent(to_wake);
    }
    return gs_sock_release(fd);
}

/* ---- Dynamic Library Loading (`sys.ffi`) ---- */

void *gs_dlopen(const char *path)
{
    if (path == NULL || path[0] == '\0') {
        return (void *)GetModuleHandleW(NULL);
    }
    wchar_t *wp = gs_utf8_to_wide(path);
    if (wp == NULL) return NULL;
    HMODULE h = LoadLibraryW(wp);
    free(wp);
    return (void *)h;
}

void *gs_dlsym(void *handle, const char *symbol)
{
    if (symbol == NULL || symbol[0] == '\0') return NULL;
    HMODULE self = GetModuleHandleW(NULL);
    HMODULE h = (handle != NULL) ? (HMODULE)handle : self;
    FARPROC p = GetProcAddress(h, symbol);
    if (p != NULL) return (void *)(uintptr_t)p;
    if (h == self) {
        static const wchar_t *const kMods[] = {
            L"ucrtbase.dll", L"api-ms-win-crt-string-l1-1-0.dll",
            L"msvcrt.dll", L"kernel32.dll"
        };
        for (size_t i = 0; i < sizeof(kMods) / sizeof(kMods[0]); i++) {
            HMODULE m = GetModuleHandleW(kMods[i]);
            if (m != NULL) {
                p = GetProcAddress(m, symbol);
                if (p != NULL) return (void *)(uintptr_t)p;
            }
        }
    }
    return NULL;
}

int32_t gs_dlclose(void *handle)
{
    if (handle == NULL) return 0;
    if ((HMODULE)handle == GetModuleHandleW(NULL)) return 0;
    return FreeLibrary((HMODULE)handle) ? 0 : -1;
}

/* ---- Subprocess & Pipe Primitives (`sys.proc`) with generational refcounted tables ---- */

typedef struct {
    HANDLE hProc;
    HANDLE hJob;
    uint32_t gen;
    uint32_t refs;
    int32_t term_sig;
    DWORD term_exit_code;
    int in_use;
    int closing;
} gs_win_proc_slot_t;

typedef struct {
    HANDLE hPipe;
    uint32_t gen;
    uint32_t refs;
    int in_use;
    int closing;
} gs_win_pipe_slot_t;

static SRWLOCK _proc_mu = SRWLOCK_INIT;
static gs_win_proc_slot_t *_proc_slots = NULL;
static uint32_t _proc_cap = 0;

static SRWLOCK _pipe_mu = SRWLOCK_INIT;
static gs_win_pipe_slot_t *_pipe_slots = NULL;
static uint32_t _pipe_cap = 0;

/* Serialize CreatePipe + CreateProcessW so inheritable child handles never overlap across spawns */
static SRWLOCK _spawn_inherit_mu = SRWLOCK_INIT;

static int32_t gs_proc_alloc_slot(HANDLE hProc, HANDLE hJob)
{
    AcquireSRWLockExclusive(&_proc_mu);
    for (uint32_t i = 1; i < _proc_cap; i++) {
        if (!_proc_slots[i].in_use) {
            if (_proc_slots[i].gen == 0) _proc_slots[i].gen = 1u;
            _proc_slots[i].hProc = hProc;
            _proc_slots[i].hJob = hJob;
            _proc_slots[i].refs = 1u;
            _proc_slots[i].term_sig = 0;
            _proc_slots[i].term_exit_code = 0;
            _proc_slots[i].in_use = 1;
            _proc_slots[i].closing = 0;
            int32_t tok = gs_handle_make(i, _proc_slots[i].gen);
            ReleaseSRWLockExclusive(&_proc_mu);
            return tok;
        }
    }
    if (_proc_cap >= (1u << GS_HANDLE_IDX_BITS)) {
        ReleaseSRWLockExclusive(&_proc_mu);
        return -1;
    }
    uint32_t new_cap = (_proc_cap == 0) ? 64u : (_proc_cap * 2u);
    if (new_cap > (1u << GS_HANDLE_IDX_BITS)) new_cap = (1u << GS_HANDLE_IDX_BITS);
    gs_win_proc_slot_t *ns = (gs_win_proc_slot_t *)realloc(
        _proc_slots, (size_t)new_cap * sizeof(gs_win_proc_slot_t));
    if (ns == NULL) {
        ReleaseSRWLockExclusive(&_proc_mu);
        return -1;
    }
    for (uint32_t i = _proc_cap; i < new_cap; i++) {
        ns[i].hProc = NULL;
        ns[i].hJob = NULL;
        ns[i].gen = 1u;
        ns[i].refs = 0u;
        ns[i].term_sig = 0;
        ns[i].term_exit_code = 0;
        ns[i].in_use = 0;
        ns[i].closing = 0;
    }
    uint32_t idx = (_proc_cap == 0) ? 1u : _proc_cap;
    ns[idx].hProc = hProc;
    ns[idx].hJob = hJob;
    ns[idx].refs = 1u;
    ns[idx].term_sig = 0;
    ns[idx].term_exit_code = 0;
    ns[idx].in_use = 1;
    ns[idx].closing = 0;
    _proc_slots = ns;
    _proc_cap = new_cap;
    int32_t tok = gs_handle_make(idx, ns[idx].gen);
    ReleaseSRWLockExclusive(&_proc_mu);
    return tok;
}

static void gs_proc_discard_slot(int32_t tok)
{
    if (tok <= 0) return;
    uint32_t idx = gs_handle_idx(tok);
    uint32_t gen = gs_handle_gen(tok);
    AcquireSRWLockExclusive(&_proc_mu);
    if (idx < _proc_cap && _proc_slots[idx].in_use && _proc_slots[idx].gen == gen) {
        _proc_slots[idx].hProc = NULL;
        _proc_slots[idx].hJob = NULL;
        _proc_slots[idx].refs = 0u;
        _proc_slots[idx].term_sig = 0;
        _proc_slots[idx].term_exit_code = 0;
        _proc_slots[idx].in_use = 0;
        _proc_slots[idx].closing = 0;
        _proc_slots[idx].gen = gs_handle_next_gen(_proc_slots[idx].gen);
    }
    ReleaseSRWLockExclusive(&_proc_mu);
}

static int gs_proc_acquire(int32_t tok, HANDLE *out_proc, HANDLE *out_job)
{
    if (tok <= 0) return 0;
    uint32_t idx = gs_handle_idx(tok);
    uint32_t gen = gs_handle_gen(tok);
    if (gen == 0) return 0;
    AcquireSRWLockExclusive(&_proc_mu);
    int ok = 0;
    if (idx < _proc_cap && _proc_slots[idx].in_use && !_proc_slots[idx].closing && _proc_slots[idx].gen == gen) {
        _proc_slots[idx].refs++;
        if (out_proc != NULL) *out_proc = _proc_slots[idx].hProc;
        if (out_job != NULL) *out_job = _proc_slots[idx].hJob;
        ok = 1;
    }
    ReleaseSRWLockExclusive(&_proc_mu);
    return ok;
}

static void gs_proc_release(int32_t tok, int mark_reaped, int32_t *out_term_sig, DWORD *out_term_exit_code)
{
    uint32_t idx = gs_handle_idx(tok);
    HANDLE hProcClose = NULL;
    HANDLE hJobClose = NULL;
    AcquireSRWLockExclusive(&_proc_mu);
    if (idx < _proc_cap && _proc_slots[idx].in_use) {
        if (out_term_sig != NULL) *out_term_sig = _proc_slots[idx].term_sig;
        if (out_term_exit_code != NULL) *out_term_exit_code = _proc_slots[idx].term_exit_code;
        if (mark_reaped && !_proc_slots[idx].closing) {
            _proc_slots[idx].closing = 1;
            if (_proc_slots[idx].refs > 0) _proc_slots[idx].refs--; /* drop owner ref */
        }
        if (_proc_slots[idx].refs > 0) _proc_slots[idx].refs--; /* drop caller ref */
        if (_proc_slots[idx].refs == 0 && _proc_slots[idx].closing) {
            hProcClose = _proc_slots[idx].hProc;
            hJobClose = _proc_slots[idx].hJob;
            _proc_slots[idx].hProc = NULL;
            _proc_slots[idx].hJob = NULL;
            _proc_slots[idx].term_sig = 0;
            _proc_slots[idx].term_exit_code = 0;
            _proc_slots[idx].in_use = 0;
            _proc_slots[idx].closing = 0;
            _proc_slots[idx].gen = gs_handle_next_gen(_proc_slots[idx].gen);
        }
    }
    ReleaseSRWLockExclusive(&_proc_mu);
    if (hProcClose != NULL) CloseHandle(hProcClose);
    if (hJobClose != NULL) CloseHandle(hJobClose);
}

/* Pipe slot indices start at 3 so 0/1/2 map directly to stdin/stdout/stderr (used by `geisha lsp`) */
static int32_t gs_pipe_alloc_slot(HANDLE h)
{
    AcquireSRWLockExclusive(&_pipe_mu);
    for (uint32_t i = 3; i < _pipe_cap; i++) {
        if (!_pipe_slots[i].in_use) {
            if (_pipe_slots[i].gen == 0) _pipe_slots[i].gen = 1u;
            _pipe_slots[i].hPipe = h;
            _pipe_slots[i].refs = 1u;
            _pipe_slots[i].in_use = 1;
            _pipe_slots[i].closing = 0;
            int32_t tok = gs_handle_make(i, _pipe_slots[i].gen);
            ReleaseSRWLockExclusive(&_pipe_mu);
            return tok;
        }
    }
    if (_pipe_cap >= (1u << GS_HANDLE_IDX_BITS)) {
        ReleaseSRWLockExclusive(&_pipe_mu);
        return -1;
    }
    uint32_t new_cap = (_pipe_cap == 0) ? 64u : (_pipe_cap * 2u);
    if (new_cap > (1u << GS_HANDLE_IDX_BITS)) new_cap = (1u << GS_HANDLE_IDX_BITS);
    gs_win_pipe_slot_t *ns = (gs_win_pipe_slot_t *)realloc(
        _pipe_slots, (size_t)new_cap * sizeof(gs_win_pipe_slot_t));
    if (ns == NULL) {
        ReleaseSRWLockExclusive(&_pipe_mu);
        return -1;
    }
    for (uint32_t i = _pipe_cap; i < new_cap; i++) {
        ns[i].hPipe = INVALID_HANDLE_VALUE;
        ns[i].gen = 1u;
        ns[i].refs = 0u;
        ns[i].in_use = 0;
        ns[i].closing = 0;
    }
    uint32_t idx = (_pipe_cap < 3u) ? 3u : _pipe_cap;
    ns[idx].hPipe = h;
    ns[idx].refs = 1u;
    ns[idx].in_use = 1;
    ns[idx].closing = 0;
    _pipe_slots = ns;
    _pipe_cap = new_cap;
    int32_t tok = gs_handle_make(idx, ns[idx].gen);
    ReleaseSRWLockExclusive(&_pipe_mu);
    return tok;
}

static HANDLE gs_pipe_acquire(int32_t tok, int *is_stdio)
{
    if (is_stdio != NULL) *is_stdio = 0;
    if (tok == 0) {
        static int stdin_bin = 0;
        if (!__atomic_load_n(&stdin_bin, __ATOMIC_ACQUIRE)) {
            int fno = _fileno(stdin);
            if (fno >= 0) (void)_setmode(fno, _O_BINARY);
            __atomic_store_n(&stdin_bin, 1, __ATOMIC_RELEASE);
        }
        if (is_stdio != NULL) *is_stdio = 1;
        return GetStdHandle(STD_INPUT_HANDLE);
    }
    if (tok == 1) {
        static int stdout_bin = 0;
        if (!__atomic_load_n(&stdout_bin, __ATOMIC_ACQUIRE)) {
            int fno = _fileno(stdout);
            if (fno >= 0) (void)_setmode(fno, _O_BINARY);
            __atomic_store_n(&stdout_bin, 1, __ATOMIC_RELEASE);
        }
        if (is_stdio != NULL) *is_stdio = 1;
        return GetStdHandle(STD_OUTPUT_HANDLE);
    }
    if (tok == 2) {
        if (is_stdio != NULL) *is_stdio = 1;
        return GetStdHandle(STD_ERROR_HANDLE);
    }
    if (tok < 3) return INVALID_HANDLE_VALUE;
    uint32_t idx = gs_handle_idx(tok);
    uint32_t gen = gs_handle_gen(tok);
    if (idx < 3u || gen == 0) return INVALID_HANDLE_VALUE;
    AcquireSRWLockExclusive(&_pipe_mu);
    HANDLE h = INVALID_HANDLE_VALUE;
    if (idx < _pipe_cap && _pipe_slots[idx].in_use && !_pipe_slots[idx].closing && _pipe_slots[idx].gen == gen) {
        _pipe_slots[idx].refs++;
        h = _pipe_slots[idx].hPipe;
    }
    ReleaseSRWLockExclusive(&_pipe_mu);
    return h;
}

static void gs_pipe_release(int32_t tok, int is_stdio)
{
    if (is_stdio) return;
    uint32_t idx = gs_handle_idx(tok);
    HANDLE to_close = INVALID_HANDLE_VALUE;
    AcquireSRWLockExclusive(&_pipe_mu);
    if (idx < _pipe_cap && _pipe_slots[idx].in_use && _pipe_slots[idx].refs > 0) {
        _pipe_slots[idx].refs--;
        if (_pipe_slots[idx].refs == 0 && _pipe_slots[idx].closing) {
            to_close = _pipe_slots[idx].hPipe;
            _pipe_slots[idx].hPipe = INVALID_HANDLE_VALUE;
            _pipe_slots[idx].in_use = 0;
            _pipe_slots[idx].closing = 0;
            _pipe_slots[idx].gen = gs_handle_next_gen(_pipe_slots[idx].gen);
        }
    }
    ReleaseSRWLockExclusive(&_pipe_mu);
    if (to_close != INVALID_HANDLE_VALUE && to_close != NULL) {
        CloseHandle(to_close);
    }
}

/* Windows CommandLineToArgvW quoting rules */
static int gs_wbuf_append_arg(gs_wbuf_t *b, const wchar_t *arg)
{
    int need_quote = (arg[0] == L'\0');
    for (const wchar_t *p = arg; *p != L'\0'; p++) {
        if (*p == L' ' || *p == L'\t' || *p == L'"' || *p == L'\n' || *p == L'\v') {
            need_quote = 1;
            break;
        }
    }
    if (!need_quote) {
        for (const wchar_t *p = arg; *p != L'\0'; p++) {
            if (gs_wbuf_push(b, *p) != 0) return -1;
        }
        return 0;
    }
    if (gs_wbuf_push(b, L'"') != 0) return -1;
    size_t bs = 0;
    for (const wchar_t *p = arg; *p != L'\0'; p++) {
        if (*p == L'\\') {
            bs++;
        } else if (*p == L'"') {
            for (size_t k = 0; k < bs * 2u + 1u; k++) {
                if (gs_wbuf_push(b, L'\\') != 0) return -1;
            }
            if (gs_wbuf_push(b, L'"') != 0) return -1;
            bs = 0;
        } else {
            for (size_t k = 0; k < bs; k++) {
                if (gs_wbuf_push(b, L'\\') != 0) return -1;
            }
            bs = 0;
            if (gs_wbuf_push(b, *p) != 0) return -1;
        }
    }
    for (size_t k = 0; k < bs * 2u; k++) {
        if (gs_wbuf_push(b, L'\\') != 0) return -1;
    }
    return gs_wbuf_push(b, L'"');
}

static int gs_wenv_key_matches(const wchar_t *entry, const wchar_t *ov)
{
    const wchar_t *eq = wcschr(ov, L'=');
    if (eq == NULL) return 0;
    size_t klen = (size_t)(eq - ov);
    return _wcsnicmp(entry, ov, klen) == 0 && entry[klen] == L'=';
}

/* Returns 0 on success (*out_env == NULL means inherit host env), -1 on error (never silently inherit). */
static int gs_build_win_env_block(int32_t env_mode, const void *env_blob, int32_t envc, wchar_t **out_env)
{
    *out_env = NULL;
    if (env_mode == 0 || (env_mode == 1 && envc <= 0)) return 0;

    wchar_t **ov_w = NULL;
    int32_t n_ov = (envc > 0) ? envc : 0;
    if (n_ov > 0) {
        if (env_blob == NULL) return -1;
        ov_w = (wchar_t **)calloc((size_t)n_ov, sizeof(wchar_t *));
        if (ov_w == NULL) return -1;
        const char *p = (const char *)env_blob;
        for (int32_t i = 0; i < n_ov; i++) {
            ov_w[i] = gs_utf8_to_wide(p);
            p += strlen(p) + 1;
            if (ov_w[i] == NULL) {
                for (int32_t k = 0; k < i; k++) free(ov_w[k]);
                free(ov_w);
                return -1;
            }
        }
    }

    gs_wbuf_t out = {NULL, 0, 0};
    if (env_mode == 1) {
        LPWCH cur_env = GetEnvironmentStringsW();
        if (cur_env == NULL) goto fail_env;
        for (const wchar_t *e = cur_env; *e != L'\0'; e += wcslen(e) + 1u) {
            int overridden = 0;
            for (int32_t i = 0; i < n_ov; i++) {
                if (gs_wenv_key_matches(e, ov_w[i])) {
                    overridden = 1;
                    break;
                }
            }
            if (!overridden) {
                for (const wchar_t *q = e; *q != L'\0'; q++) {
                    if (gs_wbuf_push(&out, *q) != 0) {
                        FreeEnvironmentStringsW(cur_env);
                        goto fail_env;
                    }
                }
                if (gs_wbuf_push(&out, L'\0') != 0) {
                    FreeEnvironmentStringsW(cur_env);
                    goto fail_env;
                }
            }
        }
        FreeEnvironmentStringsW(cur_env);
    }

    for (int32_t i = 0; i < n_ov; i++) {
        int shadowed = 0;
        for (int32_t j = i + 1; j < n_ov; j++) {
            if (gs_wenv_key_matches(ov_w[i], ov_w[j])) {
                shadowed = 1;
                break;
            }
        }
        if (!shadowed) {
            for (const wchar_t *q = ov_w[i]; *q != L'\0'; q++) {
                if (gs_wbuf_push(&out, *q) != 0) goto fail_env;
            }
            if (gs_wbuf_push(&out, L'\0') != 0) goto fail_env;
        }
    }
    if (gs_wbuf_push(&out, L'\0') != 0) goto fail_env;
    if (out.len == 1 && gs_wbuf_push(&out, L'\0') != 0) goto fail_env;

    for (int32_t i = 0; i < n_ov; i++) free(ov_w[i]);
    free(ov_w);
    *out_env = out.buf;
    return 0;

fail_env:
    free(out.buf);
    for (int32_t i = 0; i < n_ov; i++) free(ov_w[i]);
    free(ov_w);
    return -1;
}

/* Prepare a child stdio handle for PROC_THREAD_ATTRIBUTE_HANDLE_LIST.
 * If a valid host handle is not marked inheritable, create a temporary inheritable duplicate
 * (stored in *dup_out for closing after CreateProcessW) so redirected host streams are never dropped.
 */
static int gs_prepare_inherit_handle(HANDLE *h_inout, HANDLE *dup_out, HANDLE *list, DWORD *count)
{
    *dup_out = INVALID_HANDLE_VALUE;
    HANDLE h = *h_inout;
    if (h == NULL || h == INVALID_HANDLE_VALUE) return 0;
    DWORD flags = 0;
    if (!GetHandleInformation(h, &flags)) return -1;
    if (!(flags & HANDLE_FLAG_INHERIT)) {
        HANDLE dup = INVALID_HANDLE_VALUE;
        if (!DuplicateHandle(
                GetCurrentProcess(), h, GetCurrentProcess(), &dup,
                0, TRUE, DUPLICATE_SAME_ACCESS)) {
            return -1;
        }
        *dup_out = dup;
        *h_inout = dup;
        h = dup;
    }
    for (DWORD i = 0; i < *count; i++) {
        if (list[i] == h) return 0;
    }
    if (*count < 3u) {
        list[(*count)++] = h;
    }
    return 0;
}

int32_t gs_proc_spawn(
    const char *program,
    const void *arg_blob,
    int32_t argc,
    const char *cwd,
    int32_t env_mode,
    const void *env_blob,
    int32_t envc,
    int32_t stdio_packed,
    int32_t own_group,
    void *out_ints
)
{
    if (program == NULL || program[0] == '\0' || argc < 1 || arg_blob == NULL || out_ints == NULL) {
        return -1;
    }

    int stdin_mode = stdio_packed & 3;
    int stdout_mode = (stdio_packed >> 2) & 3;
    int stderr_mode = (stdio_packed >> 4) & 3;

    /* Build Win32 command line from arg_blob (argv[0] = program) */
    gs_wbuf_t cmdline = {NULL, 0, 0};
    {
        const char *p = (const char *)arg_blob;
        for (int32_t i = 0; i < argc; i++) {
            if (i > 0 && gs_wbuf_push(&cmdline, L' ') != 0) {
                free(cmdline.buf);
                return -1;
            }
            wchar_t *warg = gs_utf8_to_wide(p);
            p += strlen(p) + 1;
            if (warg == NULL || gs_wbuf_append_arg(&cmdline, warg) != 0) {
                free(warg);
                free(cmdline.buf);
                return -1;
            }
            free(warg);
        }
    }

    wchar_t *wcwd = NULL;
    if (cwd != NULL && cwd[0] != '\0') {
        wcwd = gs_utf8_to_wide(cwd);
        if (wcwd == NULL) {
            free(cmdline.buf);
            return -1;
        }
    }

    wchar_t *wenv = NULL;
    if (gs_build_win_env_block(env_mode, env_blob, envc, &wenv) != 0) {
        free(cmdline.buf);
        free(wcwd);
        return -1;
    }

    HANDLE in_r = INVALID_HANDLE_VALUE, in_w = INVALID_HANDLE_VALUE;
    HANDLE out_r = INVALID_HANDLE_VALUE, out_w = INVALID_HANDLE_VALUE;
    HANDLE err_r = INVALID_HANDLE_VALUE, err_w = INVALID_HANDLE_VALUE;
    HANDLE nul_r = INVALID_HANDLE_VALUE, nul_w = INVALID_HANDLE_VALUE;
    HANDLE dup_std[3] = { INVALID_HANDLE_VALUE, INVALID_HANDLE_VALUE, INVALID_HANDLE_VALUE };
    LPPROC_THREAD_ATTRIBUTE_LIST attr_list = NULL;
    int attr_inited = 0;

    SECURITY_ATTRIBUTES sa;
    sa.nLength = sizeof(sa);
    sa.lpSecurityDescriptor = NULL;
    sa.bInheritHandle = TRUE;

    AcquireSRWLockExclusive(&_spawn_inherit_mu);

    if (stdin_mode == 2) {
        if (!CreatePipe(&in_r, &in_w, &sa, 0)) goto fail_spawn;
        if (!SetHandleInformation(in_w, HANDLE_FLAG_INHERIT, 0)) goto fail_spawn;
    } else if (stdin_mode == 1) {
        nul_r = CreateFileW(L"NUL", GENERIC_READ, FILE_SHARE_READ | FILE_SHARE_WRITE, &sa, OPEN_EXISTING, 0, NULL);
        if (nul_r == INVALID_HANDLE_VALUE) goto fail_spawn;
    }

    if (stdout_mode == 2) {
        if (!CreatePipe(&out_r, &out_w, &sa, 0)) goto fail_spawn;
        if (!SetHandleInformation(out_r, HANDLE_FLAG_INHERIT, 0)) goto fail_spawn;
    }
    if (stderr_mode == 2) {
        if (!CreatePipe(&err_r, &err_w, &sa, 0)) goto fail_spawn;
        if (!SetHandleInformation(err_r, HANDLE_FLAG_INHERIT, 0)) goto fail_spawn;
    }
    if (stdout_mode == 1 || stderr_mode == 1) {
        nul_w = CreateFileW(L"NUL", GENERIC_WRITE, FILE_SHARE_READ | FILE_SHARE_WRITE, &sa, OPEN_EXISTING, 0, NULL);
        if (nul_w == INVALID_HANDLE_VALUE) goto fail_spawn;
    }

    STARTUPINFOEXW siex;
    memset(&siex, 0, sizeof(siex));
    siex.StartupInfo.cb = sizeof(siex);
    siex.StartupInfo.dwFlags = STARTF_USESTDHANDLES;
    siex.StartupInfo.hStdInput  = (stdin_mode == 2) ? in_r : (stdin_mode == 1 ? nul_r : GetStdHandle(STD_INPUT_HANDLE));
    siex.StartupInfo.hStdOutput = (stdout_mode == 2) ? out_w : (stdout_mode == 1 ? nul_w : GetStdHandle(STD_OUTPUT_HANDLE));
    siex.StartupInfo.hStdError  = (stderr_mode == 2) ? err_w : (stderr_mode == 1 ? nul_w : GetStdHandle(STD_ERROR_HANDLE));

    /* Restrict inheritance strictly to the child's stdio handles via PROC_THREAD_ATTRIBUTE_HANDLE_LIST */
    HANDLE inherit_list[3];
    DWORD inherit_count = 0;
    if (gs_prepare_inherit_handle(&siex.StartupInfo.hStdInput,  &dup_std[0], inherit_list, &inherit_count) != 0) goto fail_spawn;
    if (gs_prepare_inherit_handle(&siex.StartupInfo.hStdOutput, &dup_std[1], inherit_list, &inherit_count) != 0) goto fail_spawn;
    if (gs_prepare_inherit_handle(&siex.StartupInfo.hStdError,  &dup_std[2], inherit_list, &inherit_count) != 0) goto fail_spawn;

    BOOL inherit_flag = FALSE;
    DWORD flags = CREATE_UNICODE_ENVIRONMENT | CREATE_SUSPENDED;
    if (own_group != 0) flags |= CREATE_NEW_PROCESS_GROUP;

    if (inherit_count > 0) {
        SIZE_T attr_sz = 0;
        (void)InitializeProcThreadAttributeList(NULL, 1, 0, &attr_sz);
        if (attr_sz == 0) goto fail_spawn;
        attr_list = (LPPROC_THREAD_ATTRIBUTE_LIST)malloc(attr_sz);
        if (attr_list == NULL) goto fail_spawn;
        if (!InitializeProcThreadAttributeList(attr_list, 1, 0, &attr_sz)) goto fail_spawn;
        attr_inited = 1;
        if (!UpdateProcThreadAttribute(
                attr_list, 0, PROC_THREAD_ATTRIBUTE_HANDLE_LIST,
                inherit_list, (SIZE_T)inherit_count * sizeof(HANDLE), NULL, NULL)) {
            goto fail_spawn;
        }
        siex.lpAttributeList = attr_list;
        inherit_flag = TRUE;
        flags |= EXTENDED_STARTUPINFO_PRESENT;
    }

    PROCESS_INFORMATION pi;
    memset(&pi, 0, sizeof(pi));
    BOOL ok = CreateProcessW(
        NULL, cmdline.buf, NULL, NULL, inherit_flag, flags,
        (LPVOID)wenv, wcwd, &siex.StartupInfo, &pi);

    /* Close child-side handles & attribute list immediately before releasing spawn lock */
    if (attr_inited) DeleteProcThreadAttributeList(attr_list);
    free(attr_list);
    attr_list = NULL;
    attr_inited = 0;
    if (in_r != INVALID_HANDLE_VALUE) { CloseHandle(in_r); in_r = INVALID_HANDLE_VALUE; }
    if (out_w != INVALID_HANDLE_VALUE) { CloseHandle(out_w); out_w = INVALID_HANDLE_VALUE; }
    if (err_w != INVALID_HANDLE_VALUE) { CloseHandle(err_w); err_w = INVALID_HANDLE_VALUE; }
    if (nul_r != INVALID_HANDLE_VALUE) { CloseHandle(nul_r); nul_r = INVALID_HANDLE_VALUE; }
    if (nul_w != INVALID_HANDLE_VALUE) { CloseHandle(nul_w); nul_w = INVALID_HANDLE_VALUE; }
    for (int k = 0; k < 3; k++) {
        if (dup_std[k] != INVALID_HANDLE_VALUE) { CloseHandle(dup_std[k]); dup_std[k] = INVALID_HANDLE_VALUE; }
    }

    ReleaseSRWLockExclusive(&_spawn_inherit_mu);

    free(cmdline.buf);
    free(wcwd);
    free(wenv);

    if (!ok) {
        if (in_w != INVALID_HANDLE_VALUE) CloseHandle(in_w);
        if (out_r != INVALID_HANDLE_VALUE) CloseHandle(out_r);
        if (err_r != INVALID_HANDLE_VALUE) CloseHandle(err_r);
        return -1;
    }

    /* Set up Job Object (for own_group) and allocate all table slots BEFORE resuming child */
    HANDLE hJob = NULL;
    int32_t proc_id = -1;
    int32_t in_fd = -1, out_fd = -1, err_fd = -1;

    if (own_group != 0) {
        hJob = CreateJobObjectW(NULL, NULL);
        if (hJob == NULL) goto fail_after_create;
        JOBOBJECT_EXTENDED_LIMIT_INFORMATION jeli;
        memset(&jeli, 0, sizeof(jeli));
        jeli.BasicLimitInformation.LimitFlags = JOB_OBJECT_LIMIT_KILL_ON_JOB_CLOSE;
        if (!SetInformationJobObject(hJob, JobObjectExtendedLimitInformation, &jeli, sizeof(jeli))) {
            goto fail_after_create;
        }
        if (!AssignProcessToJobObject(hJob, pi.hProcess)) {
            goto fail_after_create;
        }
    }

    proc_id = gs_proc_alloc_slot(pi.hProcess, hJob);
    if (proc_id < 0) goto fail_after_create;

    if (in_w != INVALID_HANDLE_VALUE) {
        in_fd = gs_pipe_alloc_slot(in_w);
        if (in_fd < 0) goto fail_after_create;
        in_w = INVALID_HANDLE_VALUE; /* owned by pipe table */
    }
    if (out_r != INVALID_HANDLE_VALUE) {
        out_fd = gs_pipe_alloc_slot(out_r);
        if (out_fd < 0) goto fail_after_create;
        out_r = INVALID_HANDLE_VALUE;
    }
    if (err_r != INVALID_HANDLE_VALUE) {
        err_fd = gs_pipe_alloc_slot(err_r);
        if (err_fd < 0) goto fail_after_create;
        err_r = INVALID_HANDLE_VALUE;
    }

    if (ResumeThread(pi.hThread) == (DWORD)-1) {
        goto fail_after_create;
    }
    CloseHandle(pi.hThread);

    int32_t *out = (int32_t *)out_ints;
    out[0] = proc_id;
    out[1] = in_fd;
    out[2] = out_fd;
    out[3] = err_fd;
    return 0;

fail_after_create:
    if (in_fd >= 0) (void)gs_pipe_close(in_fd);
    if (out_fd >= 0) (void)gs_pipe_close(out_fd);
    if (err_fd >= 0) (void)gs_pipe_close(err_fd);
    if (in_w != INVALID_HANDLE_VALUE) CloseHandle(in_w);
    if (out_r != INVALID_HANDLE_VALUE) CloseHandle(out_r);
    if (err_r != INVALID_HANDLE_VALUE) CloseHandle(err_r);
    if (proc_id > 0) gs_proc_discard_slot(proc_id);
    if (hJob != NULL) {
        (void)TerminateJobObject(hJob, 1u);
        CloseHandle(hJob);
    }
    (void)TerminateProcess(pi.hProcess, 1u);
    (void)WaitForSingleObject(pi.hProcess, 5000u);
    CloseHandle(pi.hThread);
    CloseHandle(pi.hProcess);
    return -1;

fail_spawn:
    if (attr_inited) DeleteProcThreadAttributeList(attr_list);
    free(attr_list);
    if (in_r != INVALID_HANDLE_VALUE) CloseHandle(in_r);
    if (in_w != INVALID_HANDLE_VALUE) CloseHandle(in_w);
    if (out_r != INVALID_HANDLE_VALUE) CloseHandle(out_r);
    if (out_w != INVALID_HANDLE_VALUE) CloseHandle(out_w);
    if (err_r != INVALID_HANDLE_VALUE) CloseHandle(err_r);
    if (err_w != INVALID_HANDLE_VALUE) CloseHandle(err_w);
    if (nul_r != INVALID_HANDLE_VALUE) CloseHandle(nul_r);
    if (nul_w != INVALID_HANDLE_VALUE) CloseHandle(nul_w);
    for (int k = 0; k < 3; k++) {
        if (dup_std[k] != INVALID_HANDLE_VALUE) CloseHandle(dup_std[k]);
    }
    ReleaseSRWLockExclusive(&_spawn_inherit_mu);
    free(cmdline.buf);
    free(wcwd);
    free(wenv);
    return -1;
}

static int64_t gs_proc_wait_ms_impl(int32_t pid, DWORD timeout_ms)
{
    HANDLE hProc = NULL;
    if (!gs_proc_acquire(pid, &hProc, NULL) || hProc == NULL) return -1;

    DWORD w = WaitForSingleObject(hProc, timeout_ms);
    if (w == WAIT_TIMEOUT) {
        gs_proc_release(pid, 0, NULL, NULL);
        return 0;
    }
    if (w != WAIT_OBJECT_0) {
        gs_proc_release(pid, 0, NULL, NULL);
        return -1;
    }

    DWORD code = 0;
    (void)GetExitCodeProcess(hProc, &code);
    int32_t term_sig = 0;
    DWORD term_exit_code = 0;
    gs_proc_release(pid, 1, &term_sig, &term_exit_code);
    /* Only report Signaled if the process actually terminated with our sentinel exit code */
    if (term_sig != 0 && code == term_exit_code) {
        return (2LL << 32) | (int64_t)(uint32_t)term_sig;
    }
    return (1LL << 32) | (int64_t)(uint32_t)code;
}

int64_t gs_proc_wait(int32_t pid, int32_t nohang)
{
    return gs_proc_wait_ms_impl(pid, nohang != 0 ? 0 : INFINITE);
}

int64_t gs_proc_wait_timeout(int32_t pid, int32_t timeout_ms)
{
    DWORD ms = (timeout_ms <= 0) ? 0 : (DWORD)timeout_ms;
    return gs_proc_wait_ms_impl(pid, ms);
}

int32_t gs_proc_signal(int32_t pid, int32_t sig_kind, int32_t own_group)
{
    if (pid <= 0) return 0;
    uint32_t idx = gs_handle_idx(pid);
    uint32_t gen = gs_handle_gen(pid);
    if (gen == 0) return 0;

    int32_t sig_num = (sig_kind == 1) ? 9 : ((sig_kind == 2) ? 2 : 15);
    /* Distinct sentinel exit code so natural exits (e.g. Exited(7)) are never misclassified as Signaled */
    UINT exit_code = 0x80000000u | (UINT)sig_num;

    int32_t rc = 0;
    AcquireSRWLockExclusive(&_proc_mu);
    if (idx < _proc_cap && _proc_slots[idx].in_use && !_proc_slots[idx].closing && _proc_slots[idx].gen == gen) {
        HANDLE hProc = _proc_slots[idx].hProc;
        HANDLE hJob = _proc_slots[idx].hJob;
        if (hProc != NULL) {
            if (own_group != 0 && hJob != NULL) {
                /* Group mode: always terminate the Job Object; failure must return -1 even if leader exited */
                if (TerminateJobObject(hJob, exit_code)) {
                    if (_proc_slots[idx].term_sig == 0) {
                        _proc_slots[idx].term_sig = sig_num;
                        _proc_slots[idx].term_exit_code = (DWORD)exit_code;
                    }
                    rc = 0;
                } else {
                    rc = -1;
                }
            } else if (WaitForSingleObject(hProc, 0) == WAIT_OBJECT_0) {
                /* Non-group mode: process already exited naturally; preserve its Exited(code) status */
                rc = 0;
            } else if (TerminateProcess(hProc, exit_code)) {
                if (_proc_slots[idx].term_sig == 0) {
                    _proc_slots[idx].term_sig = sig_num;
                    _proc_slots[idx].term_exit_code = (DWORD)exit_code;
                }
                rc = 0;
            } else {
                DWORD exit_cur = 0;
                rc = (GetExitCodeProcess(hProc, &exit_cur) && exit_cur != STILL_ACTIVE) ? 0 : -1;
            }
        }
    }
    ReleaseSRWLockExclusive(&_proc_mu);
    return rc;
}

int32_t gs_pipe_read(int32_t fd, void *buf, int32_t cap)
{
    if (fd < 0 || buf == NULL || cap <= 0) return -1;
    int is_stdio = 0;
    HANDLE h = gs_pipe_acquire(fd, &is_stdio);
    if (h == INVALID_HANDLE_VALUE || h == NULL) return -1;
    DWORD n = 0;
    int32_t rc = -1;
    if (ReadFile(h, buf, (DWORD)cap, &n, NULL)) {
        rc = (int32_t)n;
    } else {
        DWORD err = GetLastError();
        if (err == ERROR_BROKEN_PIPE || err == ERROR_HANDLE_EOF) rc = 0;
    }
    gs_pipe_release(fd, is_stdio);
    return rc;
}

int32_t gs_pipe_write(int32_t fd, const void *buf, int32_t len)
{
    if (fd < 0) return -1;
    if (buf == NULL || len <= 0) return 0;
    int is_stdio = 0;
    HANDLE h = gs_pipe_acquire(fd, &is_stdio);
    if (h == INVALID_HANDLE_VALUE || h == NULL) return -1;
    const unsigned char *p = (const unsigned char *)buf;
    int32_t rem = len;
    int32_t rc = len;
    while (rem > 0) {
        DWORD written = 0;
        if (!WriteFile(h, p, (DWORD)rem, &written, NULL) || written == 0) {
            rc = -1;
            break;
        }
        p += written;
        rem -= (int32_t)written;
    }
    gs_pipe_release(fd, is_stdio);
    return rc;
}

int32_t gs_pipe_close(int32_t fd)
{
    if (fd < 3) return 0;
    uint32_t idx = gs_handle_idx(fd);
    uint32_t gen = gs_handle_gen(fd);
    if (idx < 3u || gen == 0) return 0;
    HANDLE to_close = INVALID_HANDLE_VALUE;
    AcquireSRWLockExclusive(&_pipe_mu);
    if (idx < _pipe_cap && _pipe_slots[idx].in_use && !_pipe_slots[idx].closing && _pipe_slots[idx].gen == gen) {
        _pipe_slots[idx].closing = 1;
        if (_pipe_slots[idx].refs > 0) _pipe_slots[idx].refs--;
        if (_pipe_slots[idx].refs == 0) {
            to_close = _pipe_slots[idx].hPipe;
            _pipe_slots[idx].hPipe = INVALID_HANDLE_VALUE;
            _pipe_slots[idx].in_use = 0;
            _pipe_slots[idx].closing = 0;
            _pipe_slots[idx].gen = gs_handle_next_gen(_pipe_slots[idx].gen);
        }
    }
    ReleaseSRWLockExclusive(&_pipe_mu);
    if (to_close != INVALID_HANDLE_VALUE && to_close != NULL) {
        return CloseHandle(to_close) ? 0 : -1;
    }
    return 0;
}

static int gs_win_pipe_ready(int32_t fd)
{
    if (fd < 0) return 0;
    int is_stdio = 0;
    HANDLE h = gs_pipe_acquire(fd, &is_stdio);
    if (h == INVALID_HANDLE_VALUE || h == NULL) return 1;
    DWORD avail = 0;
    int ready = 1;
    if (PeekNamedPipe(h, NULL, 0, NULL, &avail, NULL)) {
        ready = (avail > 0) ? 1 : 0;
    }
    gs_pipe_release(fd, is_stdio);
    return ready;
}

int32_t gs_pipe_poll2(int32_t fd0, int32_t fd1, int32_t timeout_ms)
{
    if (fd0 < 0 && fd1 < 0) return 0;
    int64_t deadline_ns = (timeout_ms >= 0)
        ? (gs_sys_time_mono_ns() + (int64_t)timeout_ms * 1000000LL)
        : -1;
    DWORD slice_ms = 1;
    for (;;) {
        int32_t mask = 0;
        if (fd0 >= 0 && gs_win_pipe_ready(fd0)) mask |= 1;
        if (fd1 >= 0 && gs_win_pipe_ready(fd1)) mask |= 2;
        if (mask != 0) return mask;
        if (timeout_ms == 0) return 0;
        if (deadline_ns >= 0) {
            int64_t rem_ns = deadline_ns - gs_sys_time_mono_ns();
            if (rem_ns <= 0) return 0;
            DWORD rem_ms = (DWORD)((rem_ns + 999999LL) / 1000000LL);
            Sleep(slice_ms < rem_ms ? slice_ms : rem_ms);
        } else {
            Sleep(slice_ms);
        }
        if (slice_ms < 4) slice_ms *= 2;
    }
}

int32_t gs_sys_shell(const char *cmd)
{
    if (cmd == NULL) return -1;
    wchar_t *wcmd = gs_utf8_to_wide(cmd);
    if (wcmd == NULL) return -1;
    int rc = _wsystem(wcmd);
    free(wcmd);
    return (int32_t)rc;
}

int32_t gs_proc_signal_group_only(int32_t pgid, int32_t sig_kind)
{
    return gs_proc_signal(pgid, sig_kind, 1);
}

int32_t gs_proc_poll_exited_no_reap(int32_t pid)
{
    HANDLE hProc = NULL;
    if (!gs_proc_acquire(pid, &hProc, NULL) || hProc == NULL) return -1;
    DWORD w = WaitForSingleObject(hProc, 0);
    gs_proc_release(pid, 0, NULL, NULL);
    if (w == WAIT_OBJECT_0) return 1;
    if (w == WAIT_TIMEOUT) return 0;
    return -1;
}

static volatile LONG g_gs_watch_stop = 0;

static BOOL WINAPI gs_watch_ctrl_handler(DWORD ctrl_type)
{
    if (ctrl_type == CTRL_C_EVENT || ctrl_type == CTRL_BREAK_EVENT || ctrl_type == CTRL_CLOSE_EVENT) {
        InterlockedExchange(&g_gs_watch_stop, 1);
        return TRUE;
    }
    return FALSE;
}

void gs_watch_install_signal_handlers(void)
{
    InterlockedExchange(&g_gs_watch_stop, 0);
    (void)SetConsoleCtrlHandler(gs_watch_ctrl_handler, TRUE);
}

int32_t gs_watch_should_stop(void)
{
    return InterlockedCompareExchange(&g_gs_watch_stop, 0, 0) != 0 ? 1 : 0;
}
