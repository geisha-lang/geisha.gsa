#if defined(__APPLE__) && !defined(_DARWIN_C_SOURCE)
#define _DARWIN_C_SOURCE
#endif
#ifndef _DEFAULT_SOURCE
#define _DEFAULT_SOURCE
#endif
#ifndef _POSIX_C_SOURCE
#define _POSIX_C_SOURCE 200809L
#endif

#include <arpa/inet.h>
#include <dirent.h>
#include <dlfcn.h>
#include <errno.h>
#include <fcntl.h>
#include <netdb.h>
#include <netinet/in.h>
#include <netinet/tcp.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <time.h>
#include <unistd.h>
#if defined(__APPLE__)
#include <mach-o/dyld.h>
#endif

/* ---- Host platform & executable path discovery (`sys.env`) ---- */

const char *gs_sys_host_os(void)
{
#if defined(__APPLE__)
    return "macos";
#elif defined(__linux__)
    return "linux";
#else
    return "posix";
#endif
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

const char *gs_sys_exe_path(void)
{
    static char resolved_buf[4096];
    static int initialized = 0;
    if (__atomic_load_n(&initialized, __ATOMIC_ACQUIRE) == 1) {
        return resolved_buf[0] != '\0' ? resolved_buf : NULL;
    }
    char tmp[4096];
    tmp[0] = '\0';
#if defined(__APPLE__)
    uint32_t sz = (uint32_t)sizeof(tmp);
    if (_NSGetExecutablePath(tmp, &sz) == 0) {
        char real_tmp[4096];
        if (realpath(tmp, real_tmp) != NULL) {
            snprintf(resolved_buf, sizeof(resolved_buf), "%s", real_tmp);
        } else {
            snprintf(resolved_buf, sizeof(resolved_buf), "%s", tmp);
        }
    }
#elif defined(__linux__)
    ssize_t n = readlink("/proc/self/exe", tmp, sizeof(tmp) - 1);
    if (n > 0) {
        tmp[n] = '\0';
        snprintf(resolved_buf, sizeof(resolved_buf), "%s", tmp);
    }
#endif
    __atomic_store_n(&initialized, 1, __ATOMIC_RELEASE);
    return resolved_buf[0] != '\0' ? resolved_buf : NULL;
}

/* ---- Filesystem helpers (`sys.fs`) ---- */

int32_t gs_sys_is_dir(const char *path)
{
    if (path == NULL) return 0;
    struct stat st;
    if (stat(path, &st) != 0) return 0;
    return S_ISDIR(st.st_mode) ? 1 : 0;
}

int32_t gs_sys_mkdir(const char *path)
{
    if (path == NULL || path[0] == '\0') return -1;
    if (mkdir(path, 0755) == 0) return 0;
    if (errno == EEXIST) {
        return gs_sys_is_dir(path) ? 0 : -1;
    }
    return -1;
}

void *gs_sys_dir_open(const char *path)
{
    if (path == NULL) return NULL;
    return (void *)opendir(path);
}

const char *gs_sys_dir_next(void *dir)
{
    if (dir == NULL) return NULL;
    DIR *d = (DIR *)dir;
    for (;;) {
        struct dirent *ent = readdir(d);
        if (ent == NULL) return NULL;
        if (strcmp(ent->d_name, ".") == 0 || strcmp(ent->d_name, "..") == 0) {
            continue;
        }
        return ent->d_name;
    }
}

int32_t gs_sys_dir_close(void *dir)
{
    if (dir == NULL) return 0;
    return closedir((DIR *)dir);
}

int64_t gs_sys_file_size(const char *path)
{
    if (path == NULL) return -1;
    struct stat st;
    if (stat(path, &st) != 0) return -1;
    if (!S_ISREG(st.st_mode)) return -1;
    return (int64_t)st.st_size;
}

void *gs_sys_mmap_open(const char *path)
{
    if (path == NULL) return NULL;
    int fd = open(path, O_RDONLY);
    if (fd < 0) return NULL;
    struct stat st;
    if (fstat(fd, &st) != 0 || !S_ISREG(st.st_mode) || st.st_size <= 0) {
        close(fd);
        return NULL;
    }
    void *mapped = mmap(NULL, (size_t)st.st_size, PROT_READ, MAP_PRIVATE, fd, 0);
    close(fd);
    if (mapped == MAP_FAILED) return NULL;
    return mapped;
}

int32_t gs_sys_mmap_close(void *ptr, int64_t len)
{
    if (ptr == NULL || len <= 0) return 0;
    return (int32_t)munmap(ptr, (size_t)len);
}

/* ---- Time helpers (`sys.time`) ---- */

int64_t gs_sys_time_now_ms(void)
{
    struct timespec ts;
    if (clock_gettime(CLOCK_REALTIME, &ts) != 0) return 0;
    return (int64_t)ts.tv_sec * 1000LL + (int64_t)(ts.tv_nsec / 1000000L);
}

int64_t gs_sys_time_mono_ms(void)
{
    struct timespec ts;
    if (clock_gettime(CLOCK_MONOTONIC, &ts) != 0) return 0;
    return (int64_t)ts.tv_sec * 1000LL + (int64_t)(ts.tv_nsec / 1000000L);
}

int64_t gs_sys_time_mono_ns(void)
{
    struct timespec ts;
    if (clock_gettime(CLOCK_MONOTONIC, &ts) != 0) return 0;
    return (int64_t)ts.tv_sec * 1000000000LL + (int64_t)ts.tv_nsec;
}

/* ---- OS entropy seed (`std.rand`) ---- */

int64_t gs_sys_rand_seed(void)
{
    uint64_t seed = 0;
#if defined(__APPLE__) || defined(__FreeBSD__) || defined(__OpenBSD__) || defined(__NetBSD__)
    arc4random_buf(&seed, sizeof(seed));
#else
    int fd = open("/dev/urandom", O_RDONLY);
    if (fd >= 0) {
        ssize_t n = read(fd, &seed, sizeof(seed));
        close(fd);
        if (n != (ssize_t)sizeof(seed)) {
            seed = (uint64_t)gs_sys_time_mono_ns() ^ ((uint64_t)getpid() << 32);
        }
    } else {
        seed = (uint64_t)gs_sys_time_mono_ns() ^ ((uint64_t)getpid() << 32);
    }
#endif
    return (int64_t)seed;
}

/* ---- POSIX TCP socket helpers (`sys.net`) ---- */

static void gs_configure_socket(int fd)
{
    int one = 1;
    setsockopt(fd, IPPROTO_TCP, TCP_NODELAY, &one, sizeof(one));
#ifdef SO_NOSIGPIPE
    setsockopt(fd, SOL_SOCKET, SO_NOSIGPIPE, &one, sizeof(one));
#endif
}

int32_t gs_net_tcp_listen(const char *host, int32_t port, int32_t backlog)
{
    if (port < 0 || port > 65535) return -1;
    int fd = socket(AF_INET, SOCK_STREAM, 0);
    if (fd < 0) return -1;

    int one = 1;
    setsockopt(fd, SOL_SOCKET, SO_REUSEADDR, &one, sizeof(one));
#ifdef SO_NOSIGPIPE
    setsockopt(fd, SOL_SOCKET, SO_NOSIGPIPE, &one, sizeof(one));
#endif

    struct sockaddr_in addr;
    memset(&addr, 0, sizeof(addr));
    addr.sin_family = AF_INET;
    addr.sin_port = htons((uint16_t)port);
    if (host == NULL || host[0] == '\0' || strcmp(host, "0.0.0.0") == 0) {
        addr.sin_addr.s_addr = htonl(INADDR_ANY);
    } else if (inet_pton(AF_INET, host, &addr.sin_addr) != 1) {
        close(fd);
        return -1;
    }

    if (bind(fd, (struct sockaddr *)&addr, sizeof(addr)) != 0) {
        close(fd);
        return -1;
    }
    int q = (backlog > 0) ? backlog : 128;
    if (listen(fd, q) != 0) {
        close(fd);
        return -1;
    }
    return (int32_t)fd;
}

int32_t gs_net_tcp_local_port(int32_t fd)
{
    struct sockaddr_in addr;
    socklen_t len = sizeof(addr);
    memset(&addr, 0, sizeof(addr));
    if (getsockname(fd, (struct sockaddr *)&addr, &len) != 0) return -1;
    return (int32_t)ntohs(addr.sin_port);
}

int32_t gs_net_tcp_accept(int32_t listen_fd)
{
    for (;;) {
        int client = accept(listen_fd, NULL, NULL);
        if (client >= 0) {
            gs_configure_socket(client);
            return (int32_t)client;
        }
        if (errno == EINTR) continue;
        return -1;
    }
}

int32_t gs_net_tcp_connect(const char *host, int32_t port)
{
    if (host == NULL || port <= 0 || port > 65535) return -1;
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

    int fd = -1;
    for (struct addrinfo *p = res; p != NULL; p = p->ai_next) {
        int cand = socket(p->ai_family, p->ai_socktype, p->ai_protocol);
        if (cand < 0) continue;
        if (connect(cand, p->ai_addr, p->ai_addrlen) == 0) {
            gs_configure_socket(cand);
            fd = cand;
            break;
        }
        close(cand);
    }
    freeaddrinfo(res);
    return (int32_t)fd;
}

int32_t gs_net_tcp_read(int32_t fd, void *buf, int32_t cap)
{
    if (buf == NULL || cap <= 0) return 0;
    for (;;) {
        ssize_t n = recv(fd, buf, (size_t)cap, 0);
        if (n >= 0) return (int32_t)n;
        if (errno == EINTR) continue;
        return -1;
    }
}

int32_t gs_net_tcp_peek(int32_t fd, void *buf, int32_t cap)
{
    if (buf == NULL || cap <= 0) return 0;
    for (;;) {
        ssize_t n = recv(fd, buf, (size_t)cap, MSG_PEEK);
        if (n >= 0) return (int32_t)n;
        if (errno == EINTR) continue;
        return -1;
    }
}

int32_t gs_net_tcp_write(int32_t fd, const void *buf, int32_t len)
{
    if (buf == NULL || len <= 0) return 0;
    int flags = 0;
#ifdef MSG_NOSIGNAL
    flags = MSG_NOSIGNAL;
#endif
    for (;;) {
        ssize_t n = send(fd, buf, (size_t)len, flags);
        if (n >= 0) return (int32_t)n;
        if (errno == EINTR) continue;
        return -1;
    }
}

int32_t gs_net_tcp_close(int32_t fd)
{
    if (fd < 0) return 0;
    return (int32_t)close(fd);
}

/* ---- Dynamic Library Loading (`sys.ffi`) ---- */

void *gs_dlopen(const char *path)
{
    if (path == NULL || path[0] == '\0') {
        return dlopen(NULL, RTLD_LAZY | RTLD_GLOBAL);
    }
    return dlopen(path, RTLD_LAZY | RTLD_GLOBAL);
}

void *gs_dlsym(void *handle, const char *symbol)
{
    if (symbol == NULL || symbol[0] == '\0') return NULL;
    return dlsym(handle != NULL ? handle : RTLD_DEFAULT, symbol);
}

int32_t gs_dlclose(void *handle)
{
    if (handle == NULL) return 0;
    return (int32_t)dlclose(handle);
}
