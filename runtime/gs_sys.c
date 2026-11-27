#ifndef _GNU_SOURCE
#define _GNU_SOURCE
#endif
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
#include <poll.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>
#if defined(__APPLE__)
#include <TargetConditionals.h>
#include <mach-o/dyld.h>
#if !TARGET_OS_IPHONE
#include <crt_externs.h>
#include <spawn.h>
#include <sys/event.h>
#endif
#else
#include <spawn.h>
extern char **environ;
#endif

int64_t gs_sys_rand_seed(void);
int64_t gs_sys_time_mono_ns(void);

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

int32_t gs_sys_write_atomic(const char *path, const void *buf, int64_t len, int32_t mode)
{
    if (path == NULL || path[0] == '\0' || len < 0 || (len > 0 && buf == NULL)) {
        return -1;
    }

    struct stat st;
    int has_explicit_mode = (mode >= 0);
    mode_t target_mode = 0644;
    if (has_explicit_mode) {
        target_mode = (mode_t)(mode & 07777);
    } else if (stat(path, &st) == 0) {
        has_explicit_mode = 1;
        target_mode = st.st_mode & 07777;
    }

    size_t plen = strlen(path);
    char *tmp_path = (char *)malloc(plen + 40);
    if (tmp_path == NULL) return -1;

    const char *slash = strrchr(path, '/');
    int fd = -1;
    uint64_t rng = (uint64_t)gs_sys_rand_seed();
    for (int attempt = 0; attempt < 32; attempt++) {
        rng = rng * 6364136223846793005ULL + 1442695040888963407ULL + (uint64_t)attempt;
        unsigned long long tag = (unsigned long long)rng;
        if (slash == NULL) {
            snprintf(tmp_path, plen + 40, ".%s.tmp.%016llx", path, tag);
        } else if (slash == path) {
            snprintf(tmp_path, plen + 40, "/.%s.tmp.%016llx", slash + 1, tag);
        } else {
            size_t dlen = (size_t)(slash - path);
            memcpy(tmp_path, path, dlen);
            snprintf(tmp_path + dlen, plen + 40 - dlen, "/.%s.tmp.%016llx", slash + 1, tag);
        }
        mode_t open_mode = has_explicit_mode ? 0600 : 0666;
        fd = open(tmp_path, O_CREAT | O_EXCL | O_WRONLY | O_CLOEXEC, open_mode);
        if (fd >= 0) break;
        if (errno != EEXIST) {
            free(tmp_path);
            return -1;
        }
    }
    if (fd < 0) {
        free(tmp_path);
        return -1;
    }

    if (has_explicit_mode) {
        if (fchmod(fd, target_mode) != 0) {
            close(fd);
            unlink(tmp_path);
            free(tmp_path);
            return -1;
        }
    }

    const unsigned char *p = (const unsigned char *)buf;
    int64_t rem = len;
    while (rem > 0) {
        size_t chunk = (rem > (int64_t)0x40000000LL) ? (size_t)0x40000000ULL : (size_t)rem;
        ssize_t n = write(fd, p, chunk);
        if (n > 0) {
            p += n;
            rem -= (int64_t)n;
        } else if (n < 0 && errno == EINTR) {
            continue;
        } else {
            close(fd);
            unlink(tmp_path);
            free(tmp_path);
            return -1;
        }
    }

    if (fsync(fd) != 0 && errno != EINVAL && errno != ENOTSUP && errno != EROFS) {
        close(fd);
        unlink(tmp_path);
        free(tmp_path);
        return -1;
    }
    if (close(fd) != 0) {
        unlink(tmp_path);
        free(tmp_path);
        return -1;
    }
    if (rename(tmp_path, path) != 0) {
        unlink(tmp_path);
        free(tmp_path);
        return -1;
    }

    free(tmp_path);
    return 0;
}

int32_t gs_sys_rename(const char *src, const char *dst)
{
    if (src == NULL || dst == NULL) return -1;
    return (rename(src, dst) == 0) ? 0 : -1;
}

int32_t gs_sys_chmod(const char *path, int32_t mode)
{
    if (path == NULL || mode < 0) return -1;
    return (chmod(path, (mode_t)(mode & 07777)) == 0) ? 0 : -1;
}

int64_t gs_sys_file_mtime_ms(const char *path)
{
    if (path == NULL) return -1;
    struct stat st;
    if (stat(path, &st) != 0) return -1;
#if defined(__APPLE__)
    return (int64_t)st.st_mtimespec.tv_sec * 1000LL + (int64_t)(st.st_mtimespec.tv_nsec / 1000000L);
#else
    return (int64_t)st.st_mtim.tv_sec * 1000LL + (int64_t)(st.st_mtim.tv_nsec / 1000000L);
#endif
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

/* ---- Benchmark black-box barriers (`std.bench`) ---- */

void gs_bench_black_box_mem(void *slot)
{
#if defined(__GNUC__) || defined(__clang__)
    __asm__ volatile("" : "+r"(slot) : : "memory");
#else
    void *volatile sink = slot;
    (void)sink;
#endif
}

void gs_bench_black_box_void(void)
{
#if defined(__GNUC__) || defined(__clang__)
    __asm__ volatile("" : : : "memory");
#else
    volatile int32_t sink = 0;
    (void)sink;
#endif
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

/* ---- Subprocess & Pipe Primitives (`sys.proc`) ---- */

static void gs_ensure_sigpipe_ignored(void)
{
    static int initialized = 0;
    if (__atomic_load_n(&initialized, __ATOMIC_ACQUIRE) == 1) return;
    struct sigaction cur;
    if (sigaction(SIGPIPE, NULL, &cur) == 0 && cur.sa_handler == SIG_DFL) {
        struct sigaction ign;
        memset(&ign, 0, sizeof(ign));
        ign.sa_handler = SIG_IGN;
        sigemptyset(&ign.sa_mask);
        (void)sigaction(SIGPIPE, &ign, NULL);
    }
    __atomic_store_n(&initialized, 1, __ATOMIC_RELEASE);
}

#if !(defined(__APPLE__) && TARGET_OS_IPHONE)
static char **gs_host_environ(void)
{
#if defined(__APPLE__)
    char ***ep = _NSGetEnviron();
    return (ep != NULL) ? *ep : NULL;
#else
    return environ;
#endif
}

static int gs_dup_above_stdio(int fd)
{
    if (fd >= 3) return fd;
#ifdef F_DUPFD_CLOEXEC
    int hi = fcntl(fd, F_DUPFD_CLOEXEC, 3);
#else
    int hi = fcntl(fd, F_DUPFD, 3);
    if (hi >= 0) (void)fcntl(hi, F_SETFD, FD_CLOEXEC);
#endif
    if (hi >= 0) {
        close(fd);
        return hi;
    }
    return fd;
}

static int gs_make_pipe(int fds[2])
{
    gs_ensure_sigpipe_ignored();
#if defined(__linux__)
    if (pipe2(fds, O_CLOEXEC) != 0) return -1;
#else
    if (pipe(fds) != 0) return -1;
    (void)fcntl(fds[0], F_SETFD, FD_CLOEXEC);
    (void)fcntl(fds[1], F_SETFD, FD_CLOEXEC);
#endif
    fds[0] = gs_dup_above_stdio(fds[0]);
    fds[1] = gs_dup_above_stdio(fds[1]);
#ifdef F_SETNOSIGPIPE
    (void)fcntl(fds[1], F_SETNOSIGPIPE, 1);
#endif
    return 0;
}

static int gs_env_key_matches(const char *entry, const char *override_entry)
{
    const char *eq = strchr(override_entry, '=');
    if (eq == NULL) return 0;
    size_t klen = (size_t)(eq - override_entry);
    return strncmp(entry, override_entry, klen) == 0 && entry[klen] == '=';
}
#endif

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
#if defined(__APPLE__) && TARGET_OS_IPHONE
    (void)program;
    (void)arg_blob;
    (void)argc;
    (void)cwd;
    (void)env_mode;
    (void)env_blob;
    (void)envc;
    (void)stdio_packed;
    (void)own_group;
    (void)out_ints;
    return -1;
#else
    if (program == NULL || program[0] == '\0' || argc < 1 || out_ints == NULL) {
        return -1;
    }

    int stdin_mode = stdio_packed & 3;
    int stdout_mode = (stdio_packed >> 2) & 3;
    int stderr_mode = (stdio_packed >> 4) & 3;

    int in_pipe[2] = {-1, -1};
    int out_pipe[2] = {-1, -1};
    int err_pipe[2] = {-1, -1};

    if (stdin_mode == 2 && gs_make_pipe(in_pipe) != 0) goto fail_pipes;
    if (stdout_mode == 2 && gs_make_pipe(out_pipe) != 0) goto fail_pipes;
    if (stderr_mode == 2 && gs_make_pipe(err_pipe) != 0) goto fail_pipes;

    char **argv = (char **)calloc((size_t)argc + 1u, sizeof(char *));
    if (argv == NULL) goto fail_pipes;
    {
        const char *p = (const char *)arg_blob;
        for (int32_t i = 0; i < argc; i++) {
            argv[i] = (char *)p;
            p += strlen(p) + 1;
        }
        argv[argc] = NULL;
    }

    char **custom_envp = NULL;
    char **spawn_envp = gs_host_environ();
    char *empty_env[1] = {NULL};
    if (spawn_envp == NULL) spawn_envp = empty_env;

    if (env_mode == 2) {
        int32_t n = (envc > 0) ? envc : 0;
        custom_envp = (char **)calloc((size_t)n + 1u, sizeof(char *));
        if (custom_envp == NULL) {
            free(argv);
            goto fail_pipes;
        }
        const char *p = (const char *)env_blob;
        for (int32_t i = 0; i < n; i++) {
            custom_envp[i] = (char *)p;
            p += strlen(p) + 1;
        }
        custom_envp[n] = NULL;
        spawn_envp = custom_envp;
    } else if (env_mode == 1 && envc > 0) {
        size_t base_count = 0;
        if (spawn_envp != NULL) {
            while (spawn_envp[base_count] != NULL) base_count++;
        }
        char **ov_ptrs = (char **)calloc((size_t)envc, sizeof(char *));
        custom_envp = (char **)calloc(base_count + (size_t)envc + 1u, sizeof(char *));
        if (ov_ptrs == NULL || custom_envp == NULL) {
            free(ov_ptrs);
            free(custom_envp);
            free(argv);
            goto fail_pipes;
        }
        const char *p = (const char *)env_blob;
        for (int32_t i = 0; i < envc; i++) {
            ov_ptrs[i] = (char *)p;
            p += strlen(p) + 1;
        }
        size_t out_idx = 0;
        for (size_t b = 0; b < base_count; b++) {
            int overridden = 0;
            for (int32_t i = 0; i < envc; i++) {
                if (gs_env_key_matches(spawn_envp[b], ov_ptrs[i])) {
                    overridden = 1;
                    break;
                }
            }
            if (!overridden) {
                custom_envp[out_idx++] = spawn_envp[b];
            }
        }
        for (int32_t i = 0; i < envc; i++) {
            /* Keep only the last override if duplicate keys were passed */
            int shadowed_later = 0;
            for (int32_t j = i + 1; j < envc; j++) {
                if (gs_env_key_matches(ov_ptrs[i], ov_ptrs[j])) {
                    shadowed_later = 1;
                    break;
                }
            }
            if (!shadowed_later) {
                custom_envp[out_idx++] = ov_ptrs[i];
            }
        }
        custom_envp[out_idx] = NULL;
        free(ov_ptrs);
        spawn_envp = custom_envp;
    }

    posix_spawn_file_actions_t actions;
    posix_spawnattr_t attr;
    if (posix_spawn_file_actions_init(&actions) != 0) {
        free(custom_envp);
        free(argv);
        goto fail_pipes;
    }
    if (posix_spawnattr_init(&attr) != 0) {
        posix_spawn_file_actions_destroy(&actions);
        free(custom_envp);
        free(argv);
        goto fail_pipes;
    }

    int rc = 0;
    if (own_group != 0) {
        rc = posix_spawnattr_setflags(&attr, POSIX_SPAWN_SETPGROUP);
        if (rc == 0) rc = posix_spawnattr_setpgroup(&attr, 0);
    }

    if (rc == 0 && cwd != NULL && cwd[0] != '\0') {
        rc = posix_spawn_file_actions_addchdir_np(&actions, cwd);
    }

    if (rc == 0) {
        if (stdin_mode == 1) {
            rc = posix_spawn_file_actions_addopen(&actions, STDIN_FILENO, "/dev/null", O_RDONLY, 0);
        } else if (stdin_mode == 2) {
            rc = posix_spawn_file_actions_adddup2(&actions, in_pipe[0], STDIN_FILENO);
        }
    }
    if (rc == 0) {
        if (stdout_mode == 1) {
            rc = posix_spawn_file_actions_addopen(&actions, STDOUT_FILENO, "/dev/null", O_WRONLY, 0);
        } else if (stdout_mode == 2) {
            rc = posix_spawn_file_actions_adddup2(&actions, out_pipe[1], STDOUT_FILENO);
        }
    }
    if (rc == 0) {
        if (stderr_mode == 1) {
            rc = posix_spawn_file_actions_addopen(&actions, STDERR_FILENO, "/dev/null", O_WRONLY, 0);
        } else if (stderr_mode == 2) {
            rc = posix_spawn_file_actions_adddup2(&actions, err_pipe[1], STDERR_FILENO);
        }
    }

    pid_t pid = -1;
    if (rc == 0) {
        rc = posix_spawnp(&pid, program, &actions, &attr, argv, spawn_envp);
    }

    posix_spawnattr_destroy(&attr);
    posix_spawn_file_actions_destroy(&actions);
    free(custom_envp);
    free(argv);

    if (rc != 0 || pid <= 0) {
        goto fail_pipes;
    }

    /* Close child-side pipe ends in parent */
    if (in_pipe[0] >= 0) close(in_pipe[0]);
    if (out_pipe[1] >= 0) close(out_pipe[1]);
    if (err_pipe[1] >= 0) close(err_pipe[1]);

    int32_t *out = (int32_t *)out_ints;
    out[0] = (int32_t)pid;
    out[1] = in_pipe[1];
    out[2] = out_pipe[0];
    out[3] = err_pipe[0];
    return 0;

fail_pipes:
    if (in_pipe[0] >= 0) close(in_pipe[0]);
    if (in_pipe[1] >= 0) close(in_pipe[1]);
    if (out_pipe[0] >= 0) close(out_pipe[0]);
    if (out_pipe[1] >= 0) close(out_pipe[1]);
    if (err_pipe[0] >= 0) close(err_pipe[0]);
    if (err_pipe[1] >= 0) close(err_pipe[1]);
    return -1;
#endif
}

#if !(defined(__APPLE__) && TARGET_OS_IPHONE)
static int64_t gs_decode_wait_status(int status)
{
    if (WIFEXITED(status)) {
        return (1LL << 32) | (int64_t)(uint32_t)WEXITSTATUS(status);
    }
    if (WIFSIGNALED(status)) {
        return (2LL << 32) | (int64_t)(uint32_t)WTERMSIG(status);
    }
    return (1LL << 32);
}
#endif

int64_t gs_proc_wait(int32_t pid, int32_t nohang)
{
#if defined(__APPLE__) && TARGET_OS_IPHONE
    (void)pid;
    (void)nohang;
    return -1;
#else
    if (pid <= 0) return -1;
    int opts = (nohang != 0) ? WNOHANG : 0;
    for (;;) {
        int status = 0;
        pid_t r = waitpid((pid_t)pid, &status, opts);
        if (r == 0) return 0;
        if (r > 0) {
            if (WIFSTOPPED(status)) {
                if (nohang != 0) return 0;
                continue;
            }
            return gs_decode_wait_status(status);
        }
        if (errno == EINTR) continue;
        return -1;
    }
#endif
}

int64_t gs_proc_wait_timeout(int32_t pid, int32_t timeout_ms)
{
#if defined(__APPLE__) && TARGET_OS_IPHONE
    (void)pid;
    (void)timeout_ms;
    return -1;
#else
    if (pid <= 0) return -1;
    int64_t first = gs_proc_wait(pid, 1);
    if (first != 0 || timeout_ms <= 0) return first;

    int64_t deadline_ns = gs_sys_time_mono_ns() + (int64_t)timeout_ms * 1000000LL;

#if defined(__APPLE__)
    int kq = kqueue();
    if (kq >= 0) {
        (void)fcntl(kq, F_SETFD, FD_CLOEXEC);
        struct kevent kev;
        EV_SET(&kev, (uintptr_t)pid, EVFILT_PROC, EV_ADD | EV_ENABLE | EV_ONESHOT, NOTE_EXIT, 0, NULL);
        int reg = kevent(kq, &kev, 1, NULL, 0, NULL);
        if (reg == 0) {
            for (;;) {
                int64_t rem_ns = deadline_ns - gs_sys_time_mono_ns();
                if (rem_ns <= 0) {
                    close(kq);
                    return gs_proc_wait(pid, 1);
                }
                struct timespec ts;
                ts.tv_sec = (time_t)(rem_ns / 1000000000LL);
                ts.tv_nsec = (long)(rem_ns % 1000000000LL);
                struct kevent out_ev;
                int nev = kevent(kq, NULL, 0, &out_ev, 1, &ts);
                if (nev > 0) {
                    close(kq);
                    return gs_proc_wait(pid, 0);
                }
                if (nev == 0) {
                    close(kq);
                    return gs_proc_wait(pid, 1);
                }
                if (errno == EINTR) continue;
                close(kq);
                return gs_proc_wait(pid, 1);
            }
        } else if (errno == ESRCH) {
            close(kq);
            return gs_proc_wait(pid, 0);
        }
        close(kq);
    }
#endif

    int slice_ms = 1;
    for (;;) {
        int64_t rem_ns = deadline_ns - gs_sys_time_mono_ns();
        if (rem_ns <= 0) {
            return gs_proc_wait(pid, 1);
        }
        int rem_ms = (int)((rem_ns + 999999LL) / 1000000LL);
        int wait_ms = (slice_ms < rem_ms) ? slice_ms : rem_ms;
        (void)poll(NULL, 0, wait_ms);
        int64_t st = gs_proc_wait(pid, 1);
        if (st != 0) return st;
        if (slice_ms < 4) slice_ms *= 2;
    }
#endif
}

int32_t gs_proc_signal(int32_t pid, int32_t sig_kind, int32_t own_group)
{
#if defined(__APPLE__) && TARGET_OS_IPHONE
    (void)pid;
    (void)sig_kind;
    (void)own_group;
    return -1;
#else
    if (pid <= 0) return -1;
    int sig = SIGTERM;
    if (sig_kind == 1) sig = SIGKILL;
    else if (sig_kind == 2) sig = SIGINT;

    if (own_group != 0) {
        if (kill(-(pid_t)pid, sig) == 0) return 0;
        if (errno == ESRCH) {
            return (kill((pid_t)pid, sig) == 0 || errno == ESRCH) ? 0 : -1;
        }
    }
    if (kill((pid_t)pid, sig) == 0 || errno == ESRCH) return 0;
    return -1;
#endif
}

int32_t gs_pipe_read(int32_t fd, void *buf, int32_t cap)
{
    if (fd < 0 || buf == NULL || cap <= 0) return -1;
    for (;;) {
        ssize_t n = read(fd, buf, (size_t)cap);
        if (n >= 0) return (int32_t)n;
        if (errno == EINTR) continue;
        return -1;
    }
}

int32_t gs_pipe_write(int32_t fd, const void *buf, int32_t len)
{
    if (fd < 0) return -1;
    if (buf == NULL || len <= 0) return 0;
    gs_ensure_sigpipe_ignored();
    const unsigned char *p = (const unsigned char *)buf;
    int32_t rem = len;
    while (rem > 0) {
        ssize_t n = write(fd, p, (size_t)rem);
        if (n > 0) {
            p += n;
            rem -= (int32_t)n;
        } else if (n < 0 && errno == EINTR) {
            continue;
        } else {
            return -1;
        }
    }
    return len;
}

int32_t gs_pipe_close(int32_t fd)
{
    if (fd < 0) return 0;
    return (close(fd) == 0) ? 0 : -1;
}

int32_t gs_pipe_poll2(int32_t fd0, int32_t fd1, int32_t timeout_ms)
{
    struct pollfd pfds[2];
    int map[2] = {0, 0};
    nfds_t nfds = 0;

    if (fd0 >= 0) {
        pfds[nfds].fd = fd0;
        pfds[nfds].events = POLLIN;
        pfds[nfds].revents = 0;
        map[nfds] = 1;
        nfds++;
    }
    if (fd1 >= 0) {
        pfds[nfds].fd = fd1;
        pfds[nfds].events = POLLIN;
        pfds[nfds].revents = 0;
        map[nfds] = 2;
        nfds++;
    }
    if (nfds == 0) return 0;

    int64_t deadline_ns = (timeout_ms >= 0)
        ? (gs_sys_time_mono_ns() + (int64_t)timeout_ms * 1000000LL)
        : -1;

    for (;;) {
        int wait_ms = -1;
        if (deadline_ns >= 0) {
            int64_t rem_ns = deadline_ns - gs_sys_time_mono_ns();
            if (rem_ns <= 0) wait_ms = 0;
            else wait_ms = (int)((rem_ns + 999999LL) / 1000000LL);
        }
        int r = poll(pfds, nfds, wait_ms);
        if (r > 0) {
            int32_t mask = 0;
            for (nfds_t i = 0; i < nfds; i++) {
                if (pfds[i].revents & (POLLIN | POLLHUP | POLLERR | POLLNVAL)) {
                    mask |= map[i];
                }
            }
            return mask;
        }
        if (r == 0) return 0;
        if (errno == EINTR) continue;
        return -1;
    }
}
