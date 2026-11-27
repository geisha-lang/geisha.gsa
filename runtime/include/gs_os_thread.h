#ifndef GS_OS_THREAD_H
#define GS_OS_THREAD_H

#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>
#include <setjmp.h>

#if defined(_WIN32)

#ifndef WIN32_LEAN_AND_MEAN
#define WIN32_LEAN_AND_MEAN
#endif
#include <windows.h>
#include <process.h>

typedef SRWLOCK gs_mutex_t;
#define GS_MUTEX_INIT SRWLOCK_INIT

typedef CONDITION_VARIABLE gs_cond_t;
#define GS_COND_INIT CONDITION_VARIABLE_INIT

typedef INIT_ONCE gs_once_t;
#define GS_ONCE_INIT INIT_ONCE_STATIC_INIT

typedef HANDLE gs_thread_t;
typedef DWORD gs_thread_id_t;
typedef DWORD gs_tls_key_t;

#define GS_TLS_DTOR_CC WINAPI
#define GS_SAVE_REGS(jb) ((void)setjmp(jb))

static inline void gs_mutex_init(gs_mutex_t *m) { InitializeSRWLock(m); }
static inline void gs_mutex_destroy(gs_mutex_t *m) { (void)m; }
static inline void gs_mutex_lock(gs_mutex_t *m) { AcquireSRWLockExclusive(m); }
static inline void gs_mutex_unlock(gs_mutex_t *m) { ReleaseSRWLockExclusive(m); }

static inline void gs_cond_init(gs_cond_t *c) { InitializeConditionVariable(c); }
static inline void gs_cond_destroy(gs_cond_t *c) { (void)c; }
static inline void gs_cond_wait(gs_cond_t *c, gs_mutex_t *m)
{
    SleepConditionVariableSRW(c, m, INFINITE, 0);
}
static inline bool gs_cond_timedwait_ms(gs_cond_t *c, gs_mutex_t *m, uint32_t timeout_ms)
{
    BOOL ok = SleepConditionVariableSRW(c, m, (DWORD)timeout_ms, 0);
    return (!ok && GetLastError() == ERROR_TIMEOUT);
}
static inline void gs_cond_signal(gs_cond_t *c) { WakeConditionVariable(c); }
static inline void gs_cond_broadcast(gs_cond_t *c) { WakeAllConditionVariable(c); }

typedef struct {
    void (*fn)(void);
} gs_win_once_ctx_t;

static BOOL CALLBACK gs_win_once_trampoline(PINIT_ONCE once, PVOID param, PVOID *ctx)
{
    (void)once;
    (void)ctx;
    gs_win_once_ctx_t *c = (gs_win_once_ctx_t *)param;
    if (c != NULL && c->fn != NULL) c->fn();
    return TRUE;
}

static inline void gs_once_run(gs_once_t *o, void (*fn)(void))
{
    gs_win_once_ctx_t c = { fn };
    InitOnceExecuteOnce(o, gs_win_once_trampoline, &c, NULL);
}

static inline gs_thread_id_t gs_thread_self_id(void) { return GetCurrentThreadId(); }
static inline bool gs_thread_id_equal(gs_thread_id_t a, gs_thread_id_t b) { return a == b; }

typedef struct {
    void *(*fn)(void *);
    void *arg;
} gs_win_thr_pack_t;

static unsigned __stdcall gs_win_thr_entry(void *p)
{
    gs_win_thr_pack_t *pack = (gs_win_thr_pack_t *)p;
    void *(*fn)(void *) = pack->fn;
    void *arg = pack->arg;
    free(pack);
    (void)fn(arg);
    return 0;
}

static inline int gs_thread_create(gs_thread_t *out, void *(*fn)(void *), void *arg, bool detached)
{
    gs_win_thr_pack_t *pack = (gs_win_thr_pack_t *)malloc(sizeof(gs_win_thr_pack_t));
    if (pack == NULL) return -1;
    pack->fn = fn;
    pack->arg = arg;
    uintptr_t h = _beginthreadex(NULL, 0, gs_win_thr_entry, pack, 0, NULL);
    if (h == 0) {
        free(pack);
        return -1;
    }
    if (detached) {
        CloseHandle((HANDLE)h);
        if (out != NULL) *out = NULL;
    } else if (out != NULL) {
        *out = (HANDLE)h;
    }
    return 0;
}

static inline void gs_thread_join(gs_thread_t t)
{
    if (t != NULL) {
        WaitForSingleObject(t, INFINITE);
        CloseHandle(t);
    }
}

static inline void gs_thread_detach(gs_thread_t t)
{
    if (t != NULL) {
        CloseHandle(t);
    }
}

static inline bool gs_tls_key_create(gs_tls_key_t *k, void (GS_TLS_DTOR_CC *dtor)(void *))
{
    *k = FlsAlloc(dtor);
    return *k != FLS_OUT_OF_INDEXES;
}

static inline bool gs_tls_set(gs_tls_key_t k, void *val)
{
    if (k == FLS_OUT_OF_INDEXES) return false;
    return FlsSetValue(k, val) != 0;
}

#else

#include <errno.h>
#include <pthread.h>
#include <time.h>

typedef pthread_mutex_t gs_mutex_t;
#define GS_MUTEX_INIT PTHREAD_MUTEX_INITIALIZER

typedef pthread_cond_t gs_cond_t;
#define GS_COND_INIT PTHREAD_COND_INITIALIZER

typedef pthread_once_t gs_once_t;
#define GS_ONCE_INIT PTHREAD_ONCE_INIT

typedef pthread_t gs_thread_t;
typedef pthread_t gs_thread_id_t;
typedef pthread_key_t gs_tls_key_t;

#define GS_TLS_DTOR_CC
#define GS_SAVE_REGS(jb) _setjmp(jb)

static inline void gs_mutex_init(gs_mutex_t *m) { pthread_mutex_init(m, NULL); }
static inline void gs_mutex_destroy(gs_mutex_t *m) { pthread_mutex_destroy(m); }
static inline void gs_mutex_lock(gs_mutex_t *m) { pthread_mutex_lock(m); }
static inline void gs_mutex_unlock(gs_mutex_t *m) { pthread_mutex_unlock(m); }

static inline void gs_cond_init(gs_cond_t *c) { pthread_cond_init(c, NULL); }
static inline void gs_cond_destroy(gs_cond_t *c) { pthread_cond_destroy(c); }
static inline void gs_cond_wait(gs_cond_t *c, gs_mutex_t *m) { pthread_cond_wait(c, m); }
static inline bool gs_cond_timedwait_ms(gs_cond_t *c, gs_mutex_t *m, uint32_t timeout_ms)
{
    struct timespec ts;
    clock_gettime(CLOCK_REALTIME, &ts);
    int64_t total_ns = (int64_t)ts.tv_nsec + (int64_t)timeout_ms * 1000000LL;
    ts.tv_sec += (time_t)(total_ns / 1000000000LL);
    ts.tv_nsec = (long)(total_ns % 1000000000LL);
    return pthread_cond_timedwait(c, m, &ts) == ETIMEDOUT;
}
static inline void gs_cond_signal(gs_cond_t *c) { pthread_cond_signal(c); }
static inline void gs_cond_broadcast(gs_cond_t *c) { pthread_cond_broadcast(c); }

static inline void gs_once_run(gs_once_t *o, void (*fn)(void)) { pthread_once(o, fn); }

static inline gs_thread_id_t gs_thread_self_id(void) { return pthread_self(); }
static inline bool gs_thread_id_equal(gs_thread_id_t a, gs_thread_id_t b) { return pthread_equal(a, b) != 0; }

static inline int gs_thread_create(gs_thread_t *out, void *(*fn)(void *), void *arg, bool detached)
{
    pthread_t tid;
    pthread_attr_t attr;
    pthread_attr_init(&attr);
    if (detached) {
        pthread_attr_setdetachstate(&attr, PTHREAD_CREATE_DETACHED);
    }
    int rc = pthread_create(&tid, &attr, fn, arg);
    pthread_attr_destroy(&attr);
    if (rc == 0 && out != NULL) {
        *out = tid;
    }
    return rc;
}

static inline void gs_thread_join(gs_thread_t t) { pthread_join(t, NULL); }
static inline void gs_thread_detach(gs_thread_t t) { pthread_detach(t); }

static inline bool gs_tls_key_create(gs_tls_key_t *k, void (*dtor)(void *))
{
    return pthread_key_create(k, dtor) == 0;
}

static inline bool gs_tls_set(gs_tls_key_t k, void *val)
{
    return pthread_setspecific(k, val) == 0;
}

#endif

#endif
