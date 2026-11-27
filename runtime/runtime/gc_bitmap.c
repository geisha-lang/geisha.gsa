#if defined(__APPLE__) && !defined(_DARWIN_C_SOURCE)
#define _DARWIN_C_SOURCE
#endif
#ifndef _DEFAULT_SOURCE
#define _DEFAULT_SOURCE
#endif
#ifndef _POSIX_C_SOURCE
#define _POSIX_C_SOURCE 200809L
#endif

#include "../include/gc_bitmap.h"
#include "../include/gs_conc.h"

#include <pthread.h>
#include <setjmp.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>

#ifndef MAP_ANON
#define MAP_ANON MAP_ANONYMOUS
#endif

#if defined(__clang__)
#define GC_NO_SANITIZE_STACK __attribute__((no_sanitize("address", "thread"), noinline))
#elif defined(__GNUC__)
#define GC_NO_SANITIZE_STACK __attribute__((no_sanitize_address, no_sanitize_thread, noinline))
#else
#define GC_NO_SANITIZE_STACK
#endif

GC_NO_SANITIZE_STACK static uintptr_t current_stack_sp(void)
{
    volatile uintptr_t sp_probe = 0;
    uintptr_t addr = (uintptr_t)&sp_probe;
    __asm__ volatile("" : "+r"(addr) :: "memory");
    return addr;
}

#define MAX_GLOBAL_ROOTS 4096
#define THR_RUNNING      0
#define THR_BLOCKED      1
#define THR_PARKED       2
#define THR_IDLE         3

#define GC_NURSERY_SIZE       (256u * 1024u)
#define GC_NURSERY_SLOTS      (GC_NURSERY_SIZE >> 3)
#define GC_NURSERY_BMAP_WORDS (GC_NURSERY_SLOTS >> 6)
#define GC_NURSERY_MAX_BYTES  512u

#define PAGE_LIST_NONE    0
#define PAGE_LIST_UNSWEPT 1
#define PAGE_LIST_FULL    2
#define PAGE_LIST_FREE    3

#define MIN_GC_THRESHOLD_BYTES   (2u * 1024u * 1024u)  /* 2 MB */
#define MIN_MAJOR_THRESHOLD_BYTES (8u * 1024u * 1024u) /* 8 MB */
#define MAX_CONSECUTIVE_MINORS   5u

/* Global safepoint flag polled by generated LLVM IR (`0` = normal, `1` = STW requested) */
int32_t __gs_gc_stw_requested = 0;

/* 31 size classes from 16 B to 4096 B (slot size includes 8-byte object header) */
static const uint16_t _class_slot_sizes[GC_NUM_CLASSES] = {
    16, 24, 32, 40, 48, 56, 64,
    80, 96, 112, 128,
    160, 192, 224, 256,
    320, 384, 448, 512,
    640, 768, 896, 1024,
    1280, 1536, 1792, 2048,
    2560, 3072, 3584, 4096
};

/* O(1) lookup: (total_bytes + 7) >> 3 -> size class [0..30] */
static uint8_t _words_to_class[513];
/* Precomputed 32-bit reciprocal multipliers for O(1) division: slot_idx = (off * mul) >> 32 */
static uint32_t _class_inv_mul[GC_NUM_CLASSES];
static pthread_once_t _tables_once = PTHREAD_ONCE_INIT;

typedef struct gc_nursery_t {
    uintptr_t cur;
    uintptr_t end;
    uintptr_t base;
    uint64_t alloc_bits[GC_NURSERY_BMAP_WORDS];
    uint64_t mark_bits[GC_NURSERY_BMAP_WORDS];
    uint32_t live_count;
    bool owned;
    struct gc_nursery_t *next;
    struct gc_nursery_t *prev;
} gc_nursery_t;

typedef struct gc_thread_t {
    /* Offset 0: thread-local 256 KB bump-pointer nursery (read directly by inline TLAB LLVM IR) */
    gc_nursery_t *nursery;

    uintptr_t root_start;
    uintptr_t safepoint_sp;
    jmp_buf safepoint_regs;
    int32_t state; /* atomic: THR_RUNNING / THR_BLOCKED / THR_PARKED / THR_IDLE */

    /* Thread-local active slab page per size class (100% lock-free allocation fast path) */
    gc_page_t *local_pages[GC_NUM_CLASSES];

    /* Thread-local remembered set for Old -> Young mutations (lock-free deduplicated via header bit) */
    uintptr_t *remset;
    size_t remset_len;
    size_t remset_cap;

    struct gc_thread_t *next;
    struct gc_thread_t *prev;
} gc_thread_t;

_Static_assert(offsetof(gc_thread_t, nursery) == 0, "inline TLAB assumes nursery at offset 0 of gc_thread_t");
_Static_assert(offsetof(gc_nursery_t, cur) == 0, "inline TLAB assumes cur at offset 0 of gc_nursery_t");
_Static_assert(offsetof(gc_nursery_t, end) == 8, "inline TLAB assumes end at offset 8 of gc_nursery_t");
_Static_assert(offsetof(gc_nursery_t, alloc_bits) == 24, "inline TLAB assumes alloc_bits at offset 24 of gc_nursery_t");

static pthread_mutex_t _gc_mu = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t _stw_park_cv = PTHREAD_COND_INITIALIZER;
static pthread_cond_t _stw_resume_cv = PTHREAD_COND_INITIALIZER;
static bool _stw_in_progress = false;

_Thread_local gc_thread_t *__gs_tls_thread = NULL;
#define _tls_thread __gs_tls_thread
static gc_thread_t *_threads_head = NULL;
static pthread_key_t _host_thr_key;
static pthread_once_t _host_key_once = PTHREAD_ONCE_INIT;

/* Non-moving 256 KB aligned bump-pointer nurseries + O(1) hash table */
static gc_nursery_t *_nurseries_head = NULL;
static gc_nursery_t **_nursery_table = NULL;
static size_t _nursery_table_cap = 0;
static size_t _nursery_table_mask = 0;
static size_t _nursery_count = 0;
static uintptr_t _min_nursery_addr = UINTPTR_MAX;
static uintptr_t _max_nursery_addr = 0;

/* Aligned 4 MB chunks + O(1) open-addressing hash table */
static gc_chunk_t *_chunks_head = NULL;
static gc_chunk_t **_chunk_table = NULL;
static size_t _chunk_table_cap = 0;
static size_t _chunk_table_mask = 0;
static size_t _chunk_count = 0;
static uintptr_t _min_chunk_addr = UINTPTR_MAX;
static uintptr_t _max_chunk_addr = 0;

/* Page lists */
static gc_page_t *_free_pages = NULL;
static size_t _free_page_count = 0;
static gc_page_t *_unswept_pages[GC_NUM_CLASSES];
static gc_page_t *_full_pages[GC_NUM_CLASSES];
static gc_page_t *_active_pages[GC_NUM_CLASSES]; /* Pages currently owned by threads */

/* Large objects (> 4096 B) + O(1) hash table keyed by payload_ptr */
static gc_large_t *_large_head = NULL;
static gc_large_t **_large_table = NULL;
static size_t _large_table_cap = 0;
static size_t _large_table_mask = 0;
static size_t _large_count = 0;
static size_t _large_total_bytes = 0;

/* Size-classed span cache for medium-large blocks (<= 1 MB, default 8 MB cap; tightened by gc_set_mem_limit; drained by gc_trim) */
#define LARGE_CACHE_MAX_BYTES           (1024u * 1024u)
#define LARGE_CACHE_BUCKETS             (LARGE_CACHE_MAX_BYTES / GC_PAGE_SIZE)
#define LARGE_CACHE_DEFAULT_TOTAL_BYTES (8u * 1024u * 1024u)
static void *_large_cache_buckets[LARGE_CACHE_BUCKETS];
static size_t _large_cache_bytes = 0;
static size_t _large_cache_limit_bytes = LARGE_CACHE_DEFAULT_TOTAL_BYTES;
static size_t _soft_mem_limit_bytes = 0; /* 0 = unlimited (proportional GOGC=100 growth) */

static void drain_large_cache_locked(void)
{
    for (size_t b = 0; b < LARGE_CACHE_BUCKETS; b++) {
        size_t msz = (b + 1u) * GC_PAGE_SIZE;
        void *p = _large_cache_buckets[b];
        _large_cache_buckets[b] = NULL;
        while (p != NULL) {
            void *next = *(void **)p;
            munmap(p, msz);
            p = next;
        }
    }
    _large_cache_bytes = 0;
}

/* Two-phase GC Cleanup registry (non-resurrecting finalizers) & External Memory Pressure */
typedef struct gc_cleanup_entry_t {
    int64_t token;
    void *owner; /* weak reference to GC payload_ptr (never scanned as root) */
    gc_cleanup_fn fn;
    void *arg;
    size_t external_bytes;
    struct gc_cleanup_entry_t *prev;
    struct gc_cleanup_entry_t *next;
} gc_cleanup_entry_t;

static gc_cleanup_entry_t *_cleanup_active_head = NULL;
static gc_cleanup_entry_t *_cleanup_pending_head = NULL;
static gc_cleanup_entry_t *_cleanup_pending_tail = NULL;
static int64_t _cleanup_next_token = 1;
static size_t _external_bytes_live = 0;
static size_t _external_bytes_since_gc = 0;
static size_t _external_gc_threshold = 64u * 1024u * 1024u; /* 64 MB initial external pressure threshold */

static void gc_drain_cleanups_unlocked(void)
{
    if (__builtin_expect(__atomic_load_n(&_cleanup_pending_head, __ATOMIC_ACQUIRE) == NULL, 1)) {
        return;
    }
    pthread_mutex_lock(&_gc_mu);
    gc_cleanup_entry_t *list = _cleanup_pending_head;
    _cleanup_pending_head = NULL;
    _cleanup_pending_tail = NULL;
    pthread_mutex_unlock(&_gc_mu);

    while (list != NULL) {
        gc_cleanup_entry_t *next = list->next;
        if (list->fn != NULL) {
            list->fn(list->arg);
        }
        free(list);
        list = next;
    }
}
static uintptr_t _min_large_addr = UINTPTR_MAX;
static uintptr_t _max_large_addr = 0;

/* Collection accounting & generational state */
static bool _generational_enabled = false;
static uint32_t _gc_epoch = 1;
static size_t _minor_collections = 0;
static size_t _major_collections = 0;
static size_t _consecutive_minors = 0;
static size_t _bytes_alloc_since_gc = 0;
static size_t _gc_threshold_bytes = MIN_GC_THRESHOLD_BYTES;
static size_t _major_threshold_bytes = MIN_MAJOR_THRESHOLD_BYTES;
static size_t _last_live_bytes = 0;
static size_t _last_major_live_bytes = 0;
static size_t _init_threshold_bytes = MIN_GC_THRESHOLD_BYTES;
static bool _gc_heap_inited = false;
static bool _thresholds_custom = false;

static pthread_mutex_t _ginit_mu = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t _ginit_cv = PTHREAD_COND_INITIALIZER;
static pthread_t _ginit_owner;

static void **_global_roots[MAX_GLOBAL_ROOTS];
static size_t _global_roots_count = 0;

/* StableHandle table (1-based indices; 0 = invalid/null handle, always traced as GC roots) */
static void **_handle_slots = NULL;
static size_t _handle_cap = 0;
static size_t _handle_used = 0;
static size_t *_handle_free = NULL;
static size_t _handle_free_len = 0;
static size_t _handle_free_cap = 0;

/* Orphaned remset entries from detached threads */
static uintptr_t *_orphan_remset = NULL;
static size_t _orphan_remset_len = 0;
static size_t _orphan_remset_cap = 0;

/* Mark stack (stores payload header address only — O(1) chunk lookup eliminates heap ptr) */
typedef struct {
    uintptr_t hdr_addr;
    size_t payload_words; /* non-zero only for large objects; 0 means read from header */
} gc_mark_item_t;

static gc_mark_item_t *_mark_stack = NULL;
static size_t _mark_stack_cap = 0;

/* ---- Forward declarations ---- */
static void gc_collect_locked(gc_thread_t *collector, bool force_major);
static bool mark_candidate_ptr(uintptr_t payload_ptr);

static void init_size_tables_once(void)
{
    size_t c = 0;
    for (size_t w = 0; w <= 512; w++) {
        size_t bytes = w * WORD_SIZE;
        while (c + 1 < GC_NUM_CLASSES && _class_slot_sizes[c] < bytes) {
            c++;
        }
        _words_to_class[w] = (uint8_t)c;
    }
    for (size_t i = 0; i < GC_NUM_CLASSES; i++) {
        uint64_t d = _class_slot_sizes[i];
        _class_inv_mul[i] = (uint32_t)((((uint64_t)1 << 32) + d - 1) / d);
    }
}

static inline void init_size_tables(void)
{
    pthread_once(&_tables_once, init_size_tables_once);
}

static inline size_t fast_slot_index(size_t off, uint8_t cls)
{
    return (size_t)(((uint64_t)off * (uint64_t)_class_inv_mul[cls]) >> 32);
}

/* ---- Intrusive doubly-linked page list helpers ---- */
static inline void page_list_push(gc_page_t **head, gc_page_t *p, uint8_t kind)
{
    p->prev = NULL;
    p->next = *head;
    if (*head != NULL) {
        (*head)->prev = p;
    }
    *head = p;
    p->list_kind = kind;
}

static inline void page_list_remove(gc_page_t **head, gc_page_t *p)
{
    if (p->prev != NULL) {
        p->prev->next = p->next;
    } else if (*head == p) {
        *head = p->next;
    }
    if (p->next != NULL) {
        p->next->prev = p->prev;
    }
    p->prev = NULL;
    p->next = NULL;
    p->list_kind = PAGE_LIST_NONE;
}

static inline gc_page_t *page_list_pop(gc_page_t **head)
{
    gc_page_t *p = *head;
    if (p != NULL) {
        page_list_remove(head, p);
    }
    return p;
}

static inline void release_page_memory(void *addr, size_t len)
{
#if defined(__APPLE__) && defined(MADV_FREE_REUSABLE)
    madvise(addr, len, MADV_FREE_REUSABLE);
#elif defined(__APPLE__) && defined(MADV_FREE)
    madvise(addr, len, MADV_FREE);
#elif defined(MADV_DONTNEED)
    madvise(addr, len, MADV_DONTNEED);
#else
    (void)addr;
    (void)len;
#endif
}

/* ---- O(1) Chunk Hash Table ---- */
static inline size_t chunk_hash(uintptr_t cbase, size_t mask)
{
    return (size_t)((cbase >> GC_CHUNK_SHIFT) * 11400714819323198485ULL) & mask;
}

static void chunk_table_grow_locked(void)
{
    size_t new_cap = (_chunk_table_cap == 0) ? 1024 : (_chunk_table_cap * 2);
    size_t new_mask = new_cap - 1;
    gc_chunk_t **nt = (gc_chunk_t **)calloc(new_cap, sizeof(gc_chunk_t *));
    if (nt == NULL) {
        fprintf(stderr, "GC chunk table allocation failed\n");
        abort();
    }
    for (size_t i = 0; i < _chunk_table_cap; i++) {
        gc_chunk_t *c = _chunk_table[i];
        if (c != NULL) {
            size_t h = chunk_hash(c->base, new_mask);
            while (nt[h] != NULL) h = (h + 1) & new_mask;
            nt[h] = c;
        }
    }
    free(_chunk_table);
    _chunk_table = nt;
    _chunk_table_cap = new_cap;
    _chunk_table_mask = new_mask;
}

static void chunk_table_insert_locked(gc_chunk_t *c)
{
    if (_chunk_count * 2 >= _chunk_table_cap) {
        chunk_table_grow_locked();
    }
    size_t h = chunk_hash(c->base, _chunk_table_mask);
    while (_chunk_table[h] != NULL) h = (h + 1) & _chunk_table_mask;
    _chunk_table[h] = c;
    _chunk_count++;
    if (c->base < _min_chunk_addr) _min_chunk_addr = c->base;
    if (c->base + GC_CHUNK_SIZE > _max_chunk_addr) _max_chunk_addr = c->base + GC_CHUNK_SIZE;
}

static void chunk_table_remove_locked(gc_chunk_t *c)
{
    if (_chunk_table == NULL || _chunk_count == 0) return;
    size_t mask = _chunk_table_mask;
    size_t h = chunk_hash(c->base, mask);
    while (_chunk_table[h] != NULL) {
        if (_chunk_table[h] == c) {
            _chunk_table[h] = NULL;
            _chunk_count--;
            /* Backward-shift deletion to preserve open-addressing probe chains */
            size_t next = (h + 1) & mask;
            while (_chunk_table[next] != NULL) {
                gc_chunk_t *cur = _chunk_table[next];
                size_t ideal = chunk_hash(cur->base, mask);
                if (((next - ideal) & mask) >= ((next - h) & mask)) {
                    _chunk_table[h] = cur;
                    _chunk_table[next] = NULL;
                    h = next;
                }
                next = (next + 1) & mask;
            }
            return;
        }
        h = (h + 1) & mask;
    }
}

static void reclaim_empty_chunks_locked(size_t keep_min_chunks)
{
    gc_chunk_t **pp = &_chunks_head;
    while (*pp != NULL && _chunk_count > keep_min_chunks) {
        gc_chunk_t *ch = *pp;
        bool all_free = true;
        for (size_t i = ch->first_data_page; i < GC_PAGES_PER_CHUNK; i++) {
            if (ch->pages[i].state != GC_PAGE_FREE) {
                all_free = false;
                break;
            }
        }
        if (all_free) {
            for (size_t i = ch->first_data_page; i < GC_PAGES_PER_CHUNK; i++) {
                gc_page_t *p = &ch->pages[i];
                if (p->list_kind == PAGE_LIST_FREE) {
                    page_list_remove(&_free_pages, p);
                    _free_page_count--;
                }
            }
            *pp = ch->next;
            chunk_table_remove_locked(ch);
            munmap((void *)ch->base, GC_CHUNK_SIZE);
        } else {
            pp = &ch->next;
        }
    }
}

/* ---- O(1) 256 KB-Aligned Bump-Pointer Nursery Hash Table ---- */
#define GC_NURSERY_SHIFT 18u /* 1 << 18 = 256 KB */

static inline size_t nursery_hash(uintptr_t nbase, size_t mask)
{
    return (size_t)((nbase >> GC_NURSERY_SHIFT) * 11400714819323198485ULL) & mask;
}

static void nursery_table_grow_locked(void)
{
    size_t new_cap = (_nursery_table_cap == 0) ? 256 : (_nursery_table_cap * 2);
    size_t new_mask = new_cap - 1;
    gc_nursery_t **nt = (gc_nursery_t **)calloc(new_cap, sizeof(gc_nursery_t *));
    if (nt == NULL) abort();
    for (size_t i = 0; i < _nursery_table_cap; i++) {
        gc_nursery_t *n = _nursery_table[i];
        if (n != NULL) {
            size_t h = nursery_hash(n->base, new_mask);
            while (nt[h] != NULL) h = (h + 1) & new_mask;
            nt[h] = n;
        }
    }
    free(_nursery_table);
    _nursery_table = nt;
    _nursery_table_cap = new_cap;
    _nursery_table_mask = new_mask;
}

static void nursery_table_insert_locked(gc_nursery_t *n)
{
    if (_nursery_count * 2 >= _nursery_table_cap) {
        nursery_table_grow_locked();
    }
    size_t h = nursery_hash(n->base, _nursery_table_mask);
    while (_nursery_table[h] != NULL) h = (h + 1) & _nursery_table_mask;
    _nursery_table[h] = n;
    _nursery_count++;
    if (n->base < _min_nursery_addr) _min_nursery_addr = n->base;
    if (n->end > _max_nursery_addr) _max_nursery_addr = n->end;
}

static void nursery_table_remove_locked(gc_nursery_t *n)
{
    if (_nursery_table == NULL || _nursery_count == 0) return;
    size_t mask = _nursery_table_mask;
    size_t h = nursery_hash(n->base, mask);
    while (_nursery_table[h] != NULL) {
        if (_nursery_table[h] == n) {
            _nursery_table[h] = NULL;
            _nursery_count--;
            size_t next = (h + 1) & mask;
            while (_nursery_table[next] != NULL) {
                gc_nursery_t *cur = _nursery_table[next];
                size_t ideal = nursery_hash(cur->base, mask);
                if (((next - ideal) & mask) >= ((next - h) & mask)) {
                    _nursery_table[h] = cur;
                    _nursery_table[next] = NULL;
                    h = next;
                }
                next = (next + 1) & mask;
            }
            return;
        }
        h = (h + 1) & mask;
    }
}

static inline gc_nursery_t *find_nursery(uintptr_t addr)
{
    if (_nursery_count == 0 || addr < _min_nursery_addr || addr >= _max_nursery_addr || _nursery_table == NULL) {
        return NULL;
    }
    uintptr_t nbase = addr & ~(uintptr_t)(GC_NURSERY_SIZE - 1);
    size_t mask = _nursery_table_mask;
    size_t h = nursery_hash(nbase, mask);
    for (;;) {
        gc_nursery_t *n = _nursery_table[h];
        if (n == NULL) return NULL;
        if (n->base == nbase) return n;
        h = (h + 1) & mask;
    }
}

static gc_nursery_t *alloc_nursery_locked(void)
{
    void *raw = mmap(NULL, GC_NURSERY_SIZE * 2, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANON, -1, 0);
    if (raw == MAP_FAILED) return NULL;
    uintptr_t raw_addr = (uintptr_t)raw;
    uintptr_t aligned = (raw_addr + GC_NURSERY_SIZE - 1) & ~(uintptr_t)(GC_NURSERY_SIZE - 1);
    size_t lead = aligned - raw_addr;
    size_t tail = (raw_addr + GC_NURSERY_SIZE * 2) - (aligned + GC_NURSERY_SIZE);
    if (lead > 0) munmap(raw, lead);
    if (tail > 0) munmap((void *)(aligned + GC_NURSERY_SIZE), tail);

    gc_nursery_t *n = (gc_nursery_t *)calloc(1, sizeof(gc_nursery_t));
    if (n == NULL) {
        munmap((void *)aligned, GC_NURSERY_SIZE);
        return NULL;
    }
    n->base = aligned;
    n->cur = aligned;
    n->end = aligned + GC_NURSERY_SIZE;
    n->live_count = 0;
    n->owned = true;
    n->prev = NULL;
    n->next = _nurseries_head;
    if (_nurseries_head != NULL) _nurseries_head->prev = n;
    _nurseries_head = n;
    nursery_table_insert_locked(n);
    _bytes_alloc_since_gc += GC_NURSERY_SIZE;
    return n;
}

static inline gc_chunk_t *find_chunk(uintptr_t addr)
{
    if (addr < _min_chunk_addr || addr >= _max_chunk_addr || _chunk_table == NULL) {
        return NULL;
    }
    uintptr_t cbase = addr & ~(uintptr_t)(GC_CHUNK_SIZE - 1);
    size_t mask = _chunk_table_mask;
    size_t h = chunk_hash(cbase, mask);
    for (;;) {
        gc_chunk_t *c = _chunk_table[h];
        if ((uintptr_t)c == cbase) return c;
        if (c == NULL) return NULL;
        h = (h + 1) & mask;
    }
}

static bool alloc_chunk_locked(void)
{
    void *raw = mmap(NULL, GC_CHUNK_SIZE * 2, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANON, -1, 0);
    if (raw == MAP_FAILED) {
        return false;
    }
    uintptr_t raw_addr = (uintptr_t)raw;
    uintptr_t aligned = (raw_addr + GC_CHUNK_SIZE - 1) & ~(uintptr_t)(GC_CHUNK_SIZE - 1);
    size_t lead = aligned - raw_addr;
    size_t tail = (raw_addr + GC_CHUNK_SIZE * 2) - (aligned + GC_CHUNK_SIZE);
    if (lead > 0) munmap(raw, lead);
    if (tail > 0) munmap((void *)(aligned + GC_CHUNK_SIZE), tail);

    gc_chunk_t *chunk = (gc_chunk_t *)aligned;
    chunk->base = aligned;
    size_t meta_bytes = sizeof(gc_chunk_t);
    size_t first_page = (meta_bytes + GC_PAGE_SIZE - 1) >> GC_PAGE_SHIFT;
    chunk->first_data_page = first_page;
    chunk->next = _chunks_head;
    _chunks_head = chunk;

    /* Push pages in reverse so lower addresses are popped first */
    for (size_t i = GC_PAGES_PER_CHUNK; i > first_page; i--) {
        size_t idx = i - 1;
        gc_page_t *p = &chunk->pages[idx];
        p->base = aligned + (idx << GC_PAGE_SHIFT);
        p->state = GC_PAGE_FREE;
        page_list_push(&_free_pages, p, PAGE_LIST_FREE);
        _free_page_count++;
    }

    chunk_table_insert_locked(chunk);
    return true;
}

/* ---- O(1) Large Object Hash Table ---- */
static inline size_t large_hash(uintptr_t ptr, size_t mask)
{
    return (size_t)((ptr >> 4) * 11400714819323198485ULL) & mask;
}

static void large_table_grow_locked(void)
{
    size_t new_cap = (_large_table_cap == 0) ? 256 : (_large_table_cap * 2);
    size_t new_mask = new_cap - 1;
    gc_large_t **nt = (gc_large_t **)calloc(new_cap, sizeof(gc_large_t *));
    if (nt == NULL) {
        fprintf(stderr, "GC large table allocation failed\n");
        abort();
    }
    for (size_t i = 0; i < _large_table_cap; i++) {
        gc_large_t *obj = _large_table[i];
        if (obj != NULL) {
            size_t h = large_hash(obj->payload_ptr, new_mask);
            while (nt[h] != NULL) h = (h + 1) & new_mask;
            nt[h] = obj;
        }
    }
    free(_large_table);
    _large_table = nt;
    _large_table_cap = new_cap;
    _large_table_mask = new_mask;
}

static void large_table_insert_locked(gc_large_t *obj)
{
    if (_large_count * 2 >= _large_table_cap) {
        large_table_grow_locked();
    }
    size_t h = large_hash(obj->payload_ptr, _large_table_mask);
    while (_large_table[h] != NULL) h = (h + 1) & _large_table_mask;
    _large_table[h] = obj;
    _large_count++;
    if (obj->payload_ptr < _min_large_addr) _min_large_addr = obj->payload_ptr;
    if (obj->payload_ptr >= _max_large_addr) _max_large_addr = obj->payload_ptr + 1;
}

static void large_table_remove_locked(gc_large_t *obj)
{
    if (_large_table == NULL) return;
    size_t mask = _large_table_mask;
    size_t h = large_hash(obj->payload_ptr, mask);
    while (_large_table[h] != NULL) {
        if (_large_table[h] == obj) {
            /* Backward-shift deletion to keep probe chains intact without tombstones */
            size_t cur = h;
            size_t next = (cur + 1) & mask;
            while (_large_table[next] != NULL) {
                size_t ideal = large_hash(_large_table[next]->payload_ptr, mask);
                if (((next - ideal) & mask) >= ((next - cur) & mask)) {
                    _large_table[cur] = _large_table[next];
                    cur = next;
                }
                next = (next + 1) & mask;
            }
            _large_table[cur] = NULL;
            _large_count--;
            return;
        }
        h = (h + 1) & mask;
    }
}

#define GC_MIN_OS_PAGE_SIZE 4096u
#define GC_LARGE_HDR_OFFSET ((sizeof(gc_large_t) + Header_size + 15u) & ~(size_t)15u)
_Static_assert(GC_LARGE_HDR_OFFSET < GC_MIN_OS_PAGE_SIZE, "large object header offset must fit within 4 KB OS page");

static inline gc_large_t *find_large_obj(uintptr_t payload_ptr)
{
    if (_large_count == 0
        || (payload_ptr & (uintptr_t)(GC_MIN_OS_PAGE_SIZE - 1u)) != GC_LARGE_HDR_OFFSET
        || payload_ptr < _min_large_addr
        || payload_ptr >= _max_large_addr) {
        return NULL;
    }
    size_t mask = _large_table_mask;
    size_t h = large_hash(payload_ptr, mask);
    for (;;) {
        gc_large_t *obj = _large_table[h];
        if (obj == NULL) return NULL;
        if (obj->payload_ptr == payload_ptr) return obj;
        h = (h + 1) & mask;
    }
}

/* ---- Thread Registry & Lock-Free Safepoint / Blocking Protocol ---- */
static bool all_threads_parked_locked(void)
{
    for (gc_thread_t *t = _threads_head; t != NULL; t = t->next) {
        if (__atomic_load_n(&t->state, __ATOMIC_SEQ_CST) == THR_RUNNING) {
            return false;
        }
    }
    return true;
}

static void link_thread_locked(gc_thread_t *t)
{
    t->prev = NULL;
    t->next = _threads_head;
    if (_threads_head != NULL) {
        _threads_head->prev = t;
    }
    _threads_head = t;
}

static void unlink_thread_locked(gc_thread_t *t)
{
    if (t->prev != NULL) {
        t->prev->next = t->next;
    } else {
        _threads_head = t->next;
    }
    if (t->next != NULL) {
        t->next->prev = t->prev;
    }
    t->prev = NULL;
    t->next = NULL;
}

static void retire_thread_local_pages_locked(gc_thread_t *t)
{
    for (size_t c = 0; c < GC_NUM_CLASSES; c++) {
        gc_page_t *p = t->local_pages[c];
        if (p != NULL) {
            t->local_pages[c] = NULL;
            /* Keep it on `_active_pages[c]`? Actually active pages are already linked in `_active_pages[c]`! */
            (void)p;
        }
    }
}

void gc_enable_generational(void)
{
    pthread_mutex_lock(&_gc_mu);
    __atomic_store_n(&_generational_enabled, true, __ATOMIC_RELEASE);
    pthread_mutex_unlock(&_gc_mu);
}

size_t gc_collection_count(void)
{
    pthread_mutex_lock(&_gc_mu);
    size_t c = _minor_collections + _major_collections;
    pthread_mutex_unlock(&_gc_mu);
    return c;
}

size_t gc_minor_collection_count(void)
{
    pthread_mutex_lock(&_gc_mu);
    size_t c = _minor_collections;
    pthread_mutex_unlock(&_gc_mu);
    return c;
}

size_t gc_major_collection_count(void)
{
    pthread_mutex_lock(&_gc_mu);
    size_t c = _major_collections;
    pthread_mutex_unlock(&_gc_mu);
    return c;
}

size_t gc_heap_live_bytes(void)
{
    pthread_mutex_lock(&_gc_mu);
    size_t b = _last_live_bytes;
    pthread_mutex_unlock(&_gc_mu);
    return b;
}

void gc_register_root(void **slot)
{
    if (slot == NULL) return;
    pthread_mutex_lock(&_gc_mu);
    for (size_t i = 0; i < _global_roots_count; i++) {
        if (_global_roots[i] == slot) {
            pthread_mutex_unlock(&_gc_mu);
            return;
        }
    }
    if (_global_roots_count >= MAX_GLOBAL_ROOTS) {
        pthread_mutex_unlock(&_gc_mu);
        fprintf(stderr, "GC fatal: MAX_GLOBAL_ROOTS (%u) exceeded\n", (unsigned)MAX_GLOBAL_ROOTS);
        abort();
    }
    _global_roots[_global_roots_count++] = slot;
    pthread_mutex_unlock(&_gc_mu);
}

void gc_run_globals_init_once(int32_t *state, void (*init_fn)(void))
{
    if (state == NULL || init_fn == NULL) return;
    if (__builtin_expect(__atomic_load_n(state, __ATOMIC_ACQUIRE) == 2, 1)) {
        return;
    }

    pthread_mutex_lock(&_ginit_mu);
    int32_t cur = __atomic_load_n(state, __ATOMIC_RELAXED);
    if (cur == 2) {
        pthread_mutex_unlock(&_ginit_mu);
        return;
    }
    pthread_t self = pthread_self();
    if (cur == 1) {
        if (pthread_equal(_ginit_owner, self)) {
            /* Re-entrant entry on the initializing thread */
            pthread_mutex_unlock(&_ginit_mu);
            return;
        }
        pthread_mutex_unlock(&_ginit_mu);

        /* Cooperate with STW GC while waiting for the initializing thread to finish */
        jmp_buf regs;
        _setjmp(regs);
        gc_enter_blocking(&regs);
        pthread_mutex_lock(&_ginit_mu);
        while (__atomic_load_n(state, __ATOMIC_RELAXED) == 1) {
            pthread_cond_wait(&_ginit_cv, &_ginit_mu);
        }
        pthread_mutex_unlock(&_ginit_mu);
        gc_leave_blocking();
        return;
    }

    __atomic_store_n(state, 1, __ATOMIC_RELAXED);
    _ginit_owner = self;
    pthread_mutex_unlock(&_ginit_mu);

    init_fn();

    pthread_mutex_lock(&_ginit_mu);
    __atomic_store_n(state, 2, __ATOMIC_RELEASE);
    pthread_cond_broadcast(&_ginit_cv);
    pthread_mutex_unlock(&_ginit_mu);
}

static void compute_default_thresholds(size_t init_size_words, size_t *minor_out, size_t *major_out)
{
    const char *env_words = getenv("GEISHA_GC_HEAP_WORDS");
    if (env_words != NULL) {
        long long parsed = strtoll(env_words, NULL, 10);
        if (parsed >= 32) {
            init_size_words = (size_t)parsed;
        }
    }
    if (init_size_words < 32) {
        init_size_words = 32;
    }

    size_t init_bytes = init_size_words * WORD_SIZE;
    /* Respect small GEISHA_GC_HEAP_WORDS for GC stress testing, otherwise floor at 2 MB */
    if (env_words == NULL && init_bytes < MIN_GC_THRESHOLD_BYTES) {
        init_bytes = MIN_GC_THRESHOLD_BYTES;
    }
    *minor_out = init_bytes;
    *major_out = (init_bytes * 4 > MIN_MAJOR_THRESHOLD_BYTES)
               ? (init_bytes * 4)
               : ((env_words != NULL) ? (init_bytes * 4) : MIN_MAJOR_THRESHOLD_BYTES);
}

void gc_init_with_stack(size_t init_size_words, void *stack_anchor)
{
    init_size_tables();

    size_t minor_b = 0, major_b = 0;
    compute_default_thresholds(init_size_words, &minor_b, &major_b);

    pthread_mutex_lock(&_gc_mu);
    while (_stw_in_progress) {
        pthread_cond_wait(&_stw_resume_cv, &_gc_mu);
    }

    if (!_gc_heap_inited) {
        if (!_thresholds_custom) {
            _init_threshold_bytes = minor_b;
            _gc_threshold_bytes = minor_b;
            _major_threshold_bytes = major_b;
        }
        if (_chunks_head == NULL) {
            if (!alloc_chunk_locked()) {
                pthread_mutex_unlock(&_gc_mu);
                fprintf(stderr, "GC initial chunk allocation failed\n");
                abort();
            }
        }
        _minor_collections = 0;
        _major_collections = 0;
        _consecutive_minors = 0;
        _bytes_alloc_since_gc = 0;
        _stw_in_progress = false;
        __atomic_store_n(&__gs_gc_stw_requested, 0, __ATOMIC_RELEASE);
        _gc_heap_inited = true;
    } else if (!_thresholds_custom && _minor_collections == 0 && _major_collections == 0) {
        _init_threshold_bytes = minor_b;
        _gc_threshold_bytes = minor_b;
        _major_threshold_bytes = major_b;
    }

    if (_tls_thread == NULL) {
        gc_thread_t *main_thr = (gc_thread_t *)calloc(1, sizeof(gc_thread_t));
        if (main_thr == NULL) {
            pthread_mutex_unlock(&_gc_mu);
            abort();
        }
        main_thr->root_start = (uintptr_t)stack_anchor;
        __atomic_store_n(&main_thr->state, THR_RUNNING, __ATOMIC_SEQ_CST);
        link_thread_locked(main_thr);
        _tls_thread = main_thr;
    } else {
        _tls_thread->root_start = (uintptr_t)stack_anchor;
        __atomic_store_n(&_tls_thread->state, THR_RUNNING, __ATOMIC_SEQ_CST);
    }
    pthread_mutex_unlock(&_gc_mu);
}

void gc_init(size_t init_size_words)
{
    void *frame = __builtin_frame_address(0);
    gc_init_with_stack(init_size_words, frame);
}

void gc_thread_attach(void *stack_anchor)
{
    if (_tls_thread != NULL) {
        return;
    }
    gc_thread_t *thr = (gc_thread_t *)calloc(1, sizeof(gc_thread_t));
    if (thr == NULL) {
        fprintf(stderr, "GC failed to allocate thread context\n");
        abort();
    }
    thr->root_start = (uintptr_t)stack_anchor;
    __atomic_store_n(&thr->state, THR_RUNNING, __ATOMIC_RELEASE);

    pthread_mutex_lock(&_gc_mu);
    while (_stw_in_progress) {
        pthread_cond_wait(&_stw_resume_cv, &_gc_mu);
    }
    link_thread_locked(thr);
    _tls_thread = thr;
    pthread_mutex_unlock(&_gc_mu);
}

void gc_thread_detach(void)
{
    gc_thread_t *thr = _tls_thread;
    if (thr == NULL) {
        return;
    }
    pthread_mutex_lock(&_gc_mu);
    if (thr->nursery != NULL) {
        thr->nursery->owned = false;
        thr->nursery = NULL;
    }
    retire_thread_local_pages_locked(thr);
    if (thr->remset_len > 0) {
        size_t need = _orphan_remset_len + thr->remset_len;
        if (need > _orphan_remset_cap) {
            size_t ncap = (_orphan_remset_cap == 0) ? 256 : _orphan_remset_cap;
            while (ncap < need) ncap *= 2;
            uintptr_t *nb = (uintptr_t *)realloc(_orphan_remset, ncap * sizeof(uintptr_t));
            if (nb == NULL) abort();
            _orphan_remset = nb;
            _orphan_remset_cap = ncap;
        }
        memcpy(_orphan_remset + _orphan_remset_len, thr->remset, thr->remset_len * sizeof(uintptr_t));
        _orphan_remset_len = need;
    }
    unlink_thread_locked(thr);
    if (_stw_in_progress && all_threads_parked_locked()) {
        pthread_cond_signal(&_stw_park_cv);
    }
    pthread_mutex_unlock(&_gc_mu);
    _tls_thread = NULL;
    free(thr->remset);
    free(thr);
}

__attribute__((noinline)) void gc_safepoint_slow(void)
{
    gc_thread_t *self = _tls_thread;
    if (self == NULL) {
        return;
    }
    if (__atomic_load_n(&__gs_gc_stw_requested, __ATOMIC_ACQUIRE) == 0) {
        return;
    }

    jmp_buf regs;
    _setjmp(regs);
    uintptr_t sp_here = current_stack_sp();

    pthread_mutex_lock(&_gc_mu);
    if (_stw_in_progress) {
        memcpy(&self->safepoint_regs, &regs, sizeof(jmp_buf));
        self->safepoint_sp = sp_here;
        __atomic_store_n(&self->state, THR_PARKED, __ATOMIC_SEQ_CST);
        if (all_threads_parked_locked()) {
            pthread_cond_signal(&_stw_park_cv);
        }
        while (_stw_in_progress) {
            pthread_cond_wait(&_stw_resume_cv, &_gc_mu);
        }
        __atomic_store_n(&self->state, THR_RUNNING, __ATOMIC_SEQ_CST);
    }
    pthread_mutex_unlock(&_gc_mu);
}

/* Lock-free fast path for entering C FFI / blocking syscalls */
void gc_enter_blocking(void *jmp_buf_on_stack)
{
    gc_thread_t *self = _tls_thread;
    if (self == NULL) {
        return;
    }
    uintptr_t sp_here = current_stack_sp();
    if (jmp_buf_on_stack != NULL) {
        memcpy(&self->safepoint_regs, jmp_buf_on_stack, sizeof(jmp_buf));
    }
    self->safepoint_sp = sp_here;
    __atomic_store_n(&self->state, THR_BLOCKED, __ATOMIC_SEQ_CST);
    if (__builtin_expect(__atomic_load_n(&__gs_gc_stw_requested, __ATOMIC_SEQ_CST) != 0, 0)) {
        pthread_mutex_lock(&_gc_mu);
        if (_stw_in_progress && all_threads_parked_locked()) {
            pthread_cond_signal(&_stw_park_cv);
        }
        pthread_mutex_unlock(&_gc_mu);
    }
}

/* Helper invoked by the naked `gc_enter_blocking_capture` stub with the caller's exact
 * `caller_sp` (SP_F, strictly above any subsequent FFI call frame) and a snapshot of the
 * caller's untouched callee-saved GPRs. */
__attribute__((used)) void __gs_enter_blocking_regs(
    uintptr_t caller_sp, const uintptr_t *regs, size_t nregs)
{
    gc_thread_t *self = _tls_thread;
    if (self == NULL) {
        return;
    }
    memset(&self->safepoint_regs, 0, sizeof(jmp_buf));
    size_t max_words = sizeof(jmp_buf) / sizeof(uintptr_t);
    size_t copy_words = (nregs < max_words) ? nregs : max_words;
    if (regs != NULL && copy_words > 0) {
        memcpy(&self->safepoint_regs, regs, copy_words * sizeof(uintptr_t));
    }
    self->safepoint_sp = caller_sp;
    __atomic_store_n(&self->state, THR_BLOCKED, __ATOMIC_SEQ_CST);
    if (__builtin_expect(__atomic_load_n(&__gs_gc_stw_requested, __ATOMIC_SEQ_CST) != 0, 0)) {
        pthread_mutex_lock(&_gc_mu);
        if (_stw_in_progress && all_threads_parked_locked()) {
            pthread_cond_signal(&_stw_park_cv);
        }
        pthread_mutex_unlock(&_gc_mu);
    }
}

#if defined(__APPLE__)
#define GS_ASM_SYM(name) "_" #name
#else
#define GS_ASM_SYM(name) #name
#endif

/* Platform-agnostic zero-arg blocking-section entry: captures the caller's untouched
 * callee-saved GPRs and exact `SP_F` without clobbering registers or exposing a dead
 * callee frame to concurrent STW stack scanning. */
#if defined(__aarch64__)
__attribute__((naked, noinline)) void gc_enter_blocking_capture(void)
{
    __asm__ volatile(
        "mov x0, sp\n\t"
        "sub sp, sp, #112\n\t"
        "stp x19, x20, [sp, #0]\n\t"
        "stp x21, x22, [sp, #16]\n\t"
        "stp x23, x24, [sp, #32]\n\t"
        "stp x25, x26, [sp, #48]\n\t"
        "stp x27, x28, [sp, #64]\n\t"
        "str x29,      [sp, #80]\n\t"
        "str x30,      [sp, #96]\n\t"
        "mov x1, sp\n\t"
        "mov x2, #11\n\t"
        "bl " GS_ASM_SYM(__gs_enter_blocking_regs) "\n\t"
        "ldr x30,      [sp, #96]\n\t"
        "add sp, sp, #112\n\t"
        "ret\n\t"
    );
}
#elif defined(__x86_64__) && defined(_WIN32)
__asm__(
    ".text\n\t"
    ".globl gc_enter_blocking_capture\n\t"
    ".def gc_enter_blocking_capture; .scl 2; .type 32; .endef\n\t"
    ".p2align 4\n\t"
    "gc_enter_blocking_capture:\n\t"
    ".seh_proc gc_enter_blocking_capture\n\t"
    "subq $104, %rsp\n\t"
    ".seh_stackalloc 104\n\t"
    ".seh_endprologue\n\t"
    "leaq 112(%rsp), %rcx\n\t"
    "movq %rbx, 32(%rsp)\n\t"
    "movq %rbp, 40(%rsp)\n\t"
    "movq %rdi, 48(%rsp)\n\t"
    "movq %rsi, 56(%rsp)\n\t"
    "movq %r12, 64(%rsp)\n\t"
    "movq %r13, 72(%rsp)\n\t"
    "movq %r14, 80(%rsp)\n\t"
    "movq %r15, 88(%rsp)\n\t"
    "leaq 32(%rsp), %rdx\n\t"
    "movl $8, %r8d\n\t"
    "call " GS_ASM_SYM(__gs_enter_blocking_regs) "\n\t"
    "addq $104, %rsp\n\t"
    "ret\n\t"
    ".seh_endproc\n"
);
#elif defined(__x86_64__)
__attribute__((naked, noinline)) void gc_enter_blocking_capture(void)
{
    __asm__ volatile(
        "leaq 8(%rsp), %rdi\n\t"
        "subq $56, %rsp\n\t"
        "movq %rbx,  0(%rsp)\n\t"
        "movq %rbp,  8(%rsp)\n\t"
        "movq %r12, 16(%rsp)\n\t"
        "movq %r13, 24(%rsp)\n\t"
        "movq %r14, 32(%rsp)\n\t"
        "movq %r15, 40(%rsp)\n\t"
        "movq %rsp, %rsi\n\t"
        "movl $6, %edx\n\t"
        "call " GS_ASM_SYM(__gs_enter_blocking_regs) "\n\t"
        "addq $56, %rsp\n\t"
        "ret\n\t"
    );
}
#else
__attribute__((noinline)) void gc_enter_blocking_capture(void)
{
    jmp_buf regs;
    _setjmp(regs);
    gc_enter_blocking(&regs);
}
#endif

/* Lock-free fast path for leaving C FFI / blocking syscalls */
void gc_leave_blocking(void)
{
    gc_thread_t *self = _tls_thread;
    if (self == NULL) {
        return;
    }
    __atomic_store_n(&self->state, THR_RUNNING, __ATOMIC_SEQ_CST);
    if (__builtin_expect(__atomic_load_n(&__gs_gc_stw_requested, __ATOMIC_SEQ_CST) != 0, 0)) {
        pthread_mutex_lock(&_gc_mu);
        if (_stw_in_progress) {
            __atomic_store_n(&self->state, THR_PARKED, __ATOMIC_SEQ_CST);
            if (all_threads_parked_locked()) {
                pthread_cond_signal(&_stw_park_cv);
            }
            while (_stw_in_progress) {
                pthread_cond_wait(&_stw_resume_cv, &_gc_mu);
            }
            __atomic_store_n(&self->state, THR_RUNNING, __ATOMIC_SEQ_CST);
        }
        pthread_mutex_unlock(&_gc_mu);
    }
}

/* ---- Sticky Generational Write Barrier (race-free under TSan & safe on stack pointers) ---- */
void gc_write_barrier(void *container_ptr)
{
    if (__builtin_expect(!__atomic_load_n(&_generational_enabled, __ATOMIC_RELAXED) || container_ptr == NULL, 0)) {
        return;
    }
    gc_thread_t *self = _tls_thread;
    if (__builtin_expect(self == NULL, 0)) {
        return;
    }

    uintptr_t addr = (uintptr_t)container_ptr;
    uintptr_t sp_here = current_stack_sp();
    if (self->root_start != 0 && sp_here <= self->root_start && addr >= sp_here - 4096u && addr <= self->root_start) {
        return;
    }

    header_t *hp = (header_t *)(addr - Header_size);
    header_t prev = __atomic_load_n(hp, __ATOMIC_RELAXED);
    if ((prev & (HEADER_OLD_BIT | HEADER_REMEMBERED_BIT)) != HEADER_OLD_BIT) {
        return;
    }

    /* Slow path (entered at most once per old-gen object per Minor GC): verify heap membership under `_gc_mu` */
    bool valid_old_heap = false;
    pthread_mutex_lock(&_gc_mu);
    gc_nursery_t *nurs = find_nursery(addr);
    if (nurs != NULL) {
        uintptr_t hdr_addr = addr - Header_size;
        if (hdr_addr >= nurs->base && hdr_addr < nurs->cur) {
            size_t slot = (hdr_addr - nurs->base) >> 3;
            valid_old_heap = ((nurs->mark_bits[slot >> 6] & (1ULL << (slot & 63u))) != 0);
        }
    } else {
        gc_chunk_t *chunk = find_chunk(addr);
        if (chunk != NULL) {
            size_t pidx = (addr - chunk->base) >> GC_PAGE_SHIFT;
            if (pidx >= chunk->first_data_page) {
                gc_page_t *page = &chunk->pages[pidx];
                uintptr_t hdr_addr = addr - Header_size;
                if (page->state == GC_PAGE_INUSE && hdr_addr >= page->base) {
                    size_t slot_idx = (hdr_addr - page->base) / page->slot_size;
                    valid_old_heap = ((page->mark_bits[slot_idx >> 6] & (1ULL << (slot_idx & 63u))) != 0);
                }
            }
        } else {
            gc_large_t *lo = find_large_obj(addr);
            valid_old_heap = (lo != NULL && lo->marked);
        }
    }
    pthread_mutex_unlock(&_gc_mu);

    if (!valid_old_heap) {
        return;
    }
    if ((__atomic_fetch_or(hp, HEADER_REMEMBERED_BIT, __ATOMIC_RELAXED) & HEADER_REMEMBERED_BIT) != 0) {
        return;
    }

    /* Append to thread-local remembered set */
    if (__builtin_expect(self->remset_len >= self->remset_cap, 0)) {
        size_t ncap = (self->remset_cap == 0) ? 256 : (self->remset_cap * 2);
        uintptr_t *nb = (uintptr_t *)realloc(self->remset, ncap * sizeof(uintptr_t));
        if (nb == NULL) {
            fprintf(stderr, "GC remset allocation failed\n");
            abort();
        }
        self->remset = nb;
        self->remset_cap = ncap;
    }
    self->remset[self->remset_len++] = addr;
}

/* ---- Lazy Sweep of a single 16 KB page (runs outside STW on refill!) ---- */
static size_t lazy_sweep_page(gc_page_t *p)
{
    size_t reclaimed_slots = 0;
    size_t slot_size = p->slot_size;
    uintptr_t base = p->base;
    /* Prepend newly dead slots (`alloc && !mark`) to existing `p->free_list` */
    for (size_t w = 0; w < GC_BITMAP_WORDS; w++) {
        uint64_t dead = p->alloc_bits[w] & ~p->mark_bits[w];
        if (dead != 0) {
            p->alloc_bits[w] &= ~dead;
            while (dead != 0) {
                unsigned bit = (unsigned)__builtin_ctzll(dead);
                dead &= dead - 1;
                uint16_t slot_idx = (uint16_t)((w << 6) + bit);
                gc_free_slot_t *s = (gc_free_slot_t *)(base + (size_t)slot_idx * slot_size);
                s->next = p->free_list;
                s->slot_idx = slot_idx;
                p->free_list = s;
                reclaimed_slots++;
            }
        }
    }
    p->sweep_gen = _gc_epoch;
    return reclaimed_slots;
}

static inline void zero_payload_words(void *payload, size_t payload_words)
{
    if (payload_words <= 16) {
        uintptr_t *p = (uintptr_t *)payload;
        for (size_t i = 0; i < payload_words; i++) {
            p[i] = 0;
        }
    } else {
        memset(payload, 0, payload_words * WORD_SIZE);
    }
}

static inline void zero_masked_words(void *payload, uint64_t mask)
{
    uintptr_t *p = (uintptr_t *)payload;
    while (mask != 0) {
        unsigned i = (unsigned)__builtin_ctzll(mask);
        mask &= mask - 1;
        p[i] = 0;
    }
}

/* Refill thread's local slab page for `cls` (holding `_gc_mu`) */
static gc_page_t *acquire_page_for_class_locked(size_t cls, gc_thread_t *self, jmp_buf *regs, bool *regs_saved, uintptr_t sp_marker)
{
    /* Trigger GC if allocation budget exceeded */
    if (_bytes_alloc_since_gc >= _gc_threshold_bytes) {
        if (self != NULL) {
            if (!*regs_saved) {
                _setjmp(*regs);
                *regs_saved = true;
            }
            memcpy(&self->safepoint_regs, regs, sizeof(jmp_buf));
            self->safepoint_sp = sp_marker;
        }
        gc_collect_locked(self, false);
    }

    /* 1. Try popping an unswept partial page for this size class and lazily sweep it */
    while (_unswept_pages[cls] != NULL) {
        gc_page_t *p = page_list_pop(&_unswept_pages[cls]);
        size_t reclaimed = lazy_sweep_page(p);
        if (p->free_list != NULL || p->bump_idx < p->num_slots) {
            _bytes_alloc_since_gc += (reclaimed * p->slot_size) + ((size_t)(p->num_slots - p->bump_idx) * p->slot_size);
            page_list_push(&_active_pages[cls], p, PAGE_LIST_NONE);
            return p;
        }
        /* Actually full after sweep */
        page_list_push(&_full_pages[cls], p, PAGE_LIST_FULL);
    }

    /* 2. Take a fresh free page (or allocate a new 4 MB chunk) */
    if (_free_pages == NULL) {
        if (!alloc_chunk_locked()) {
            /* Last resort: force major GC and retry */
            if (self != NULL) {
                if (!*regs_saved) {
                    _setjmp(*regs);
                    *regs_saved = true;
                }
                memcpy(&self->safepoint_regs, regs, sizeof(jmp_buf));
                self->safepoint_sp = sp_marker;
            }
            gc_collect_locked(self, true);
            if (_free_pages == NULL && !alloc_chunk_locked()) {
                return NULL;
            }
        }
    }

    gc_page_t *p = page_list_pop(&_free_pages);
    _free_page_count--;
    uint16_t slot_sz = _class_slot_sizes[cls];
    p->state = GC_PAGE_INUSE;
    p->size_class = (uint8_t)cls;
    p->slot_size = slot_sz;
    p->num_slots = (uint16_t)(GC_PAGE_SIZE / slot_sz);
    p->bump_idx = 0;
    p->live_count = 0;
    p->free_list = NULL;
    p->sweep_gen = _gc_epoch;
    memset(p->alloc_bits, 0, sizeof(p->alloc_bits));
    memset(p->mark_bits, 0, sizeof(p->mark_bits));

    _bytes_alloc_since_gc += GC_PAGE_SIZE;
    page_list_push(&_active_pages[cls], p, PAGE_LIST_NONE);
    return p;
}

static void *alloc_large_object(size_t size_bytes, size_t payload_words, bool noscan, bool zero_init, bool has_mask, uint64_t ptr_mask)
{
    gc_thread_t *self = _tls_thread;
    jmp_buf regs;
    bool regs_saved = false;
    uintptr_t sp_here = current_stack_sp();

    size_t hdr_offset = (sizeof(gc_large_t) + Header_size + 15u) & ~(size_t)15u;
    size_t map_size = (hdr_offset + payload_words * WORD_SIZE + GC_PAGE_SIZE - 1) & ~(GC_PAGE_SIZE - 1);

    pthread_mutex_lock(&_gc_mu);
    while (_stw_in_progress) {
        if (self != NULL) {
            if (!regs_saved) {
                _setjmp(regs);
                regs_saved = true;
            }
            memcpy(&self->safepoint_regs, &regs, sizeof(jmp_buf));
            self->safepoint_sp = sp_here;
            __atomic_store_n(&self->state, THR_PARKED, __ATOMIC_SEQ_CST);
            if (all_threads_parked_locked()) pthread_cond_signal(&_stw_park_cv);
        }
        pthread_cond_wait(&_stw_resume_cv, &_gc_mu);
        if (self != NULL) __atomic_store_n(&self->state, THR_RUNNING, __ATOMIC_SEQ_CST);
    }

    if (_bytes_alloc_since_gc + map_size >= _gc_threshold_bytes) {
        if (self != NULL) {
            if (!regs_saved) {
                _setjmp(regs);
                regs_saved = true;
            }
            memcpy(&self->safepoint_regs, &regs, sizeof(jmp_buf));
            self->safepoint_sp = sp_here;
        }
        gc_collect_locked(self, false);
    }

    void *raw = NULL;
    bool from_cache = false;
    if (map_size >= GC_PAGE_SIZE && map_size <= LARGE_CACHE_MAX_BYTES) {
        size_t b = (map_size >> GC_PAGE_SHIFT) - 1u;
        if (_large_cache_buckets[b] != NULL) {
            raw = _large_cache_buckets[b];
            _large_cache_buckets[b] = *(void **)raw;
            if (_large_cache_bytes >= map_size) _large_cache_bytes -= map_size;
            else _large_cache_bytes = 0;
            from_cache = true;
        }
    }
    if (raw == NULL) {
        raw = mmap(NULL, map_size, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANON, -1, 0);
    }
    if (raw == MAP_FAILED) {
        drain_large_cache_locked();
        if (self != NULL) {
            if (!regs_saved) {
                _setjmp(regs);
                regs_saved = true;
            }
            memcpy(&self->safepoint_regs, &regs, sizeof(jmp_buf));
            self->safepoint_sp = sp_here;
        }
        gc_collect_locked(self, true);
        drain_large_cache_locked();
        raw = mmap(NULL, map_size, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANON, -1, 0);
        if (raw == MAP_FAILED) {
            pthread_mutex_unlock(&_gc_mu);
            fprintf(stderr, "GC out of memory allocating large object (%zu bytes)\n", size_bytes);
            abort();
        }
    }

    gc_large_t *lo = (gc_large_t *)raw;
    uintptr_t payload_ptr = (uintptr_t)raw + hdr_offset;
    header_t *hp = (header_t *)(payload_ptr - Header_size);
    *hp = make_gc_header(payload_words, noscan, has_mask, ptr_mask);

    lo->map_size = map_size;
    lo->payload_words = payload_words;
    lo->payload_ptr = payload_ptr;
    lo->marked = false;
    lo->prev = NULL;
    lo->next = _large_head;
    if (_large_head != NULL) _large_head->prev = lo;
    _large_head = lo;
    large_table_insert_locked(lo);

    _large_total_bytes += map_size;
    _bytes_alloc_since_gc += map_size;
    pthread_mutex_unlock(&_gc_mu);
    gc_drain_cleanups_unlocked();

    if (from_cache) {
        if (has_mask) {
            zero_masked_words((void *)payload_ptr, ptr_mask);
        } else if (zero_init) {
            memset((void *)payload_ptr, 0, payload_words * WORD_SIZE);
        }
    }
    return (void *)payload_ptr;
}

__attribute__((noinline)) static void *alloc_small_slow(
    size_t size_bytes, size_t payload_words, size_t cls,
    bool noscan, bool zero_init, bool has_mask, uint64_t ptr_mask)
{
    gc_thread_t *self = _tls_thread;
    jmp_buf regs;
    bool regs_saved = false;
    uintptr_t sp_here = current_stack_sp();

    pthread_mutex_lock(&_gc_mu);
    while (_stw_in_progress) {
        if (self != NULL) {
            if (!regs_saved) {
                _setjmp(regs);
                regs_saved = true;
            }
            memcpy(&self->safepoint_regs, &regs, sizeof(jmp_buf));
            self->safepoint_sp = sp_here;
            __atomic_store_n(&self->state, THR_PARKED, __ATOMIC_SEQ_CST);
            if (all_threads_parked_locked()) pthread_cond_signal(&_stw_park_cv);
        }
        pthread_cond_wait(&_stw_resume_cv, &_gc_mu);
        if (self != NULL) __atomic_store_n(&self->state, THR_RUNNING, __ATOMIC_SEQ_CST);
    }

    /* Move exhausted local page (if any) from `_active_pages[cls]` to `_full_pages[cls]` */
    if (self != NULL && self->local_pages[cls] != NULL) {
        gc_page_t *old_p = self->local_pages[cls];
        if (old_p->free_list == NULL && old_p->bump_idx >= old_p->num_slots) {
            page_list_remove(&_active_pages[cls], old_p);
            page_list_push(&_full_pages[cls], old_p, PAGE_LIST_FULL);
            self->local_pages[cls] = NULL;
        }
    }

    gc_page_t *p = (self != NULL && self->local_pages[cls] != NULL)
                 ? self->local_pages[cls]
                 : acquire_page_for_class_locked(cls, self, &regs, &regs_saved, sp_here);

    if (p == NULL) {
        pthread_mutex_unlock(&_gc_mu);
        fprintf(stderr, "GC out of memory allocating %zu bytes\n", size_bytes);
        abort();
    }

    if (self != NULL) {
        self->local_pages[cls] = p;
    }

    void *slot_raw;
    uint16_t slot_idx;
    if (p->free_list != NULL) {
        gc_free_slot_t *s = p->free_list;
        p->free_list = s->next;
        slot_idx = s->slot_idx;
        slot_raw = (void *)s;
    } else {
        slot_idx = p->bump_idx++;
        slot_raw = (void *)(p->base + (size_t)slot_idx * p->slot_size);
    }
    p->alloc_bits[slot_idx >> 6] |= (1ULL << (slot_idx & 63u));
    header_t *hdr = (header_t *)slot_raw;
    *hdr = make_gc_header(payload_words, noscan, has_mask, ptr_mask);

    pthread_mutex_unlock(&_gc_mu);
    gc_drain_cleanups_unlocked();

    void *payload = (void *)(hdr + 1);
    if (has_mask) {
        zero_masked_words(payload, ptr_mask);
    } else if (zero_init) {
        zero_payload_words(payload, payload_words);
    }
    return payload;
}

__attribute__((noinline)) static void *alloc_nursery_slow(
    size_t size_bytes, size_t payload_words,
    bool noscan, bool zero_init, bool has_mask, uint64_t ptr_mask)
{
    gc_thread_t *self = _tls_thread;
    jmp_buf regs;
    bool regs_saved = false;
    uintptr_t sp_here = current_stack_sp();
    size_t total_bytes = (payload_words + 1) * WORD_SIZE;

    pthread_mutex_lock(&_gc_mu);
    while (_stw_in_progress) {
        if (self != NULL) {
            if (!regs_saved) {
                _setjmp(regs);
                regs_saved = true;
            }
            memcpy(&self->safepoint_regs, &regs, sizeof(jmp_buf));
            self->safepoint_sp = sp_here;
            __atomic_store_n(&self->state, THR_PARKED, __ATOMIC_SEQ_CST);
            if (all_threads_parked_locked()) pthread_cond_signal(&_stw_park_cv);
        }
        pthread_cond_wait(&_stw_resume_cv, &_gc_mu);
        if (self != NULL) __atomic_store_n(&self->state, THR_RUNNING, __ATOMIC_SEQ_CST);
    }

    if (_bytes_alloc_since_gc >= _gc_threshold_bytes) {
        if (self != NULL) {
            if (!regs_saved) {
                _setjmp(regs);
                regs_saved = true;
            }
            memcpy(&self->safepoint_regs, &regs, sizeof(jmp_buf));
            self->safepoint_sp = sp_here;
        }
        gc_collect_locked(self, false);
    }

    gc_nursery_t *n = (self != NULL) ? self->nursery : NULL;
    if (n != NULL && n->cur + total_bytes > n->end) {
        n->owned = false;
        self->nursery = NULL;
        n = NULL;
    }
    if (n == NULL) {
        n = alloc_nursery_locked();
        if (n == NULL) {
            pthread_mutex_unlock(&_gc_mu);
            size_t cls = _words_to_class[payload_words + 1];
            return alloc_small_slow(size_bytes, payload_words, cls, noscan, zero_init, has_mask, ptr_mask);
        }
        if (self != NULL) {
            self->nursery = n;
        } else {
            n->owned = false;
        }
    }

    uintptr_t cur = n->cur;
    n->cur = cur + total_bytes;
    size_t slot = (cur - n->base) >> 3;
    n->alloc_bits[slot >> 6] |= (1ULL << (slot & 63u));
    header_t *hdr = (header_t *)cur;
    *hdr = make_gc_header(payload_words, noscan, has_mask, ptr_mask);
    pthread_mutex_unlock(&_gc_mu);
    gc_drain_cleanups_unlocked();

    void *payload = (void *)(hdr + 1);
    if (has_mask) {
        zero_masked_words(payload, ptr_mask);
    } else if (zero_init) {
        zero_payload_words(payload, payload_words);
    }
    return payload;
}

static inline void *gc_alloc_inline(
    size_t size_bytes, bool noscan, bool zero_init, bool has_mask, uint64_t ptr_mask)
{
    size_t payload_words = (size_bytes + WORD_SIZE - 1) / WORD_SIZE;
    if (payload_words == 0) payload_words = 1;
    size_t total_words = payload_words + 1;

    if (__builtin_expect(total_words > (GC_MAX_SMALL_BYTES / WORD_SIZE), 0)) {
        return alloc_large_object(size_bytes, payload_words, noscan, zero_init, has_mask, ptr_mask);
    }

    gc_thread_t *self = _tls_thread;
    /* Fast 3-instruction Bump-Pointer Nursery path for small objects (<= 512 B) */
    if (__builtin_expect(
            total_words <= (GC_NURSERY_MAX_BYTES / WORD_SIZE) &&
            self != NULL &&
            __atomic_load_n(&__gs_gc_stw_requested, __ATOMIC_RELAXED) == 0,
            1)) {
        gc_nursery_t *n = self->nursery;
        if (__builtin_expect(n != NULL, 1)) {
            size_t total_bytes = total_words * WORD_SIZE;
            uintptr_t cur = n->cur;
            uintptr_t next = cur + total_bytes;
            if (__builtin_expect(next <= n->end, 1)) {
                n->cur = next;
                size_t slot = (cur - n->base) >> 3;
                n->alloc_bits[slot >> 6] |= (1ULL << (slot & 63u));
                header_t *hdr = (header_t *)cur;
                *hdr = make_gc_header(payload_words, noscan, has_mask, ptr_mask);

                void *payload = (void *)(hdr + 1);
                if (has_mask) {
                    zero_masked_words(payload, ptr_mask);
                } else if (zero_init) {
                    zero_payload_words(payload, payload_words);
                }
                return payload;
            }
        }
        return alloc_nursery_slow(size_bytes, payload_words, noscan, zero_init, has_mask, ptr_mask);
    }

    size_t cls = _words_to_class[total_words];
    if (__builtin_expect(
            self != NULL &&
            __atomic_load_n(&__gs_gc_stw_requested, __ATOMIC_RELAXED) == 0,
            1)) {
        gc_page_t *p = self->local_pages[cls];
        if (__builtin_expect(p != NULL, 1)) {
            void *slot_raw;
            uint16_t slot_idx;
            if (p->free_list != NULL) {
                gc_free_slot_t *s = p->free_list;
                p->free_list = s->next;
                slot_idx = s->slot_idx;
                slot_raw = (void *)s;
            } else if (__builtin_expect(p->bump_idx < p->num_slots, 1)) {
                slot_idx = p->bump_idx++;
                slot_raw = (void *)(p->base + (size_t)slot_idx * p->slot_size);
            } else {
                return alloc_small_slow(size_bytes, payload_words, cls, noscan, zero_init, has_mask, ptr_mask);
            }

            p->alloc_bits[slot_idx >> 6] |= (1ULL << (slot_idx & 63u));
            header_t *hdr = (header_t *)slot_raw;
            *hdr = make_gc_header(payload_words, noscan, has_mask, ptr_mask);

            void *payload = (void *)(hdr + 1);
            if (has_mask) {
                zero_masked_words(payload, ptr_mask);
            } else if (zero_init) {
                zero_payload_words(payload, payload_words);
            }
            return payload;
        }
    }

    return alloc_small_slow(size_bytes, payload_words, cls, noscan, zero_init, has_mask, ptr_mask);
}

void *gc_alloc(size_t size_bytes)
{
    return gc_alloc_inline(size_bytes, false, true, false, 0);
}

void *gc_alloc_atomic(size_t size_bytes)
{
    return gc_alloc_inline(size_bytes, true, true, false, 0);
}

void *gc_alloc_atomic_uninit(size_t size_bytes)
{
    return gc_alloc_inline(size_bytes, true, false, false, 0);
}

void *gc_alloc_masked(size_t size_bytes, uint64_t ptr_mask)
{
    return gc_alloc_inline(size_bytes, false, false, true, ptr_mask);
}

/* ---- Marking Engine (O(1) Lookup + Exact Pointer Mask + Prefetch) ---- */
static inline void mark_stack_push(uintptr_t hdr_addr, size_t large_words, size_t *sp)
{
    if (__builtin_expect(*sp >= _mark_stack_cap, 0)) {
        size_t next_cap = (_mark_stack_cap == 0) ? 4096 : (_mark_stack_cap * 2);
        gc_mark_item_t *grown = (gc_mark_item_t *)realloc(_mark_stack, next_cap * sizeof(gc_mark_item_t));
        if (grown == NULL) {
            fprintf(stderr, "GC mark stack allocation failed\n");
            abort();
        }
        _mark_stack = grown;
        _mark_stack_cap = next_cap;
    }
    _mark_stack[*sp].hdr_addr = hdr_addr;
    _mark_stack[*sp].payload_words = large_words;
    (*sp)++;
}

/* Mark a candidate pointer (returns true iff newly marked 0 -> 1) and push onto mark stack if scannable */
static inline bool try_mark_ptr_push(uintptr_t payload_ptr, size_t *sp)
{
    if (payload_ptr == 0 || (payload_ptr & (WORD_SIZE - 1)) != 0) {
        return false;
    }

    gc_nursery_t *nurs = find_nursery(payload_ptr);
    if (nurs != NULL) {
        uintptr_t hdr_addr = payload_ptr - Header_size;
        if (hdr_addr < nurs->base || hdr_addr >= nurs->cur) return false;
        size_t slot = (hdr_addr - nurs->base) >> 3;
        size_t widx = slot >> 6;
        uint64_t bit = 1ULL << (slot & 63u);
        if ((nurs->alloc_bits[widx] & bit) == 0) return false;
        if ((nurs->mark_bits[widx] & bit) != 0) return false;

        nurs->mark_bits[widx] |= bit;
        nurs->live_count++;
        header_t *hp = (header_t *)hdr_addr;
        header_t hdr = __atomic_load_n(hp, __ATOMIC_RELAXED) | HEADER_OLD_BIT;
        __atomic_store_n(hp, hdr, __ATOMIC_RELAXED);
        if (!Is_noscan_hdr(hdr)) {
            __builtin_prefetch((const void *)payload_ptr, 0, 1);
            mark_stack_push(hdr_addr, 0, sp);
        }
        return true;
    }

    gc_chunk_t *chunk = find_chunk(payload_ptr);
    if (__builtin_expect(chunk != NULL, 1)) {
        size_t pidx = (payload_ptr - chunk->base) >> GC_PAGE_SHIFT;
        if (pidx < chunk->first_data_page) return false;
        gc_page_t *page = &chunk->pages[pidx];
        if (page->state != GC_PAGE_INUSE) return false;
        uintptr_t hdr_addr = payload_ptr - Header_size;
        if (hdr_addr < page->base) return false;
        size_t off = hdr_addr - page->base;
        size_t slot_sz = page->slot_size;
        size_t slot_idx = fast_slot_index(off, page->size_class);
        if (slot_idx * slot_sz != off) return false;

        size_t widx = slot_idx >> 6;
        uint64_t bit = 1ULL << (slot_idx & 63u);
        if ((page->alloc_bits[widx] & bit) == 0) return false;
        if ((page->mark_bits[widx] & bit) != 0) return false;

        page->mark_bits[widx] |= bit;
        page->live_count++;

        header_t *hp = (header_t *)hdr_addr;
        header_t hdr = __atomic_load_n(hp, __ATOMIC_RELAXED) | HEADER_OLD_BIT;
        __atomic_store_n(hp, hdr, __ATOMIC_RELAXED);
        if (!Is_noscan_hdr(hdr)) {
            __builtin_prefetch((const void *)payload_ptr, 0, 1);
            mark_stack_push(hdr_addr, 0, sp);
        }
        return true;
    }

    gc_large_t *lo = find_large_obj(payload_ptr);
    if (lo != NULL && !lo->marked) {
        lo->marked = true;
        uintptr_t hdr_addr = payload_ptr - Header_size;
        header_t *hp = (header_t *)hdr_addr;
        header_t hdr = __atomic_load_n(hp, __ATOMIC_RELAXED) | HEADER_OLD_BIT;
        __atomic_store_n(hp, hdr, __ATOMIC_RELAXED);
        if (!Is_noscan_hdr(hdr)) {
            mark_stack_push(hdr_addr, lo->payload_words, sp);
        }
        return true;
    }

    return false;
}

static void drain_mark_stack(size_t *sp)
{
    while (*sp > 0) {
        (*sp)--;
        uintptr_t hdr_addr = _mark_stack[*sp].hdr_addr;
        size_t large_words = _mark_stack[*sp].payload_words;
        header_t hdr_val = *(const header_t *)hdr_addr;
        if (Is_noscan_hdr(hdr_val)) continue;

        const uintptr_t *fields = (const uintptr_t *)(hdr_addr + Header_size);
        if (Has_ptr_mask_hdr(hdr_val)) {
            uint64_t mask = Get_ptr_mask_hdr(hdr_val);
            while (mask != 0) {
                unsigned i = (unsigned)__builtin_ctzll(mask);
                mask &= mask - 1;
                uintptr_t val = fields[i];
                if (val != 0) {
                    try_mark_ptr_push(val, sp);
                }
            }
        } else {
            size_t payload_words = (large_words != 0) ? large_words : Get_payload_words_hdr(hdr_val);
            for (size_t i = 0; i < payload_words; i++) {
                uintptr_t val = fields[i];
                if (val != 0) {
                    try_mark_ptr_push(val, sp);
                }
            }
        }
    }
}

static bool mark_candidate_ptr(uintptr_t payload_ptr)
{
    size_t sp = 0;
    bool newly = try_mark_ptr_push(payload_ptr, &sp);
    if (sp > 0) {
        drain_mark_stack(&sp);
    }
    return newly;
}

static void scan_object_children_only(uintptr_t payload_ptr)
{
    uintptr_t hdr_addr = payload_ptr - Header_size;
    header_t hdr_val = *(const header_t *)hdr_addr;
    if (Is_noscan_hdr(hdr_val)) return;

    size_t sp = 0;
    const uintptr_t *fields = (const uintptr_t *)payload_ptr;
    if (Has_ptr_mask_hdr(hdr_val)) {
        uint64_t mask = Get_ptr_mask_hdr(hdr_val);
        while (mask != 0) {
            unsigned i = (unsigned)__builtin_ctzll(mask);
            mask &= mask - 1;
            uintptr_t val = fields[i];
            if (val != 0) {
                try_mark_ptr_push(val, &sp);
            }
        }
    } else {
        gc_large_t *lo = find_large_obj(payload_ptr);
        size_t payload_words = (lo != NULL) ? lo->payload_words : Get_payload_words_hdr(hdr_val);
        for (size_t i = 0; i < payload_words; i++) {
            uintptr_t val = fields[i];
            if (val != 0) {
                try_mark_ptr_push(val, &sp);
            }
        }
    }
    if (sp > 0) {
        drain_mark_stack(&sp);
    }
}

bool gc_is_obj_marked(const void *payload_ptr)
{
    uintptr_t addr = (uintptr_t)payload_ptr;
    if (addr == 0 || (addr & (WORD_SIZE - 1)) != 0) return false;

    gc_nursery_t *nurs = find_nursery(addr);
    if (nurs != NULL) {
        uintptr_t hdr_addr = addr - Header_size;
        if (hdr_addr < nurs->base || hdr_addr >= nurs->cur) return false;
        size_t slot = (hdr_addr - nurs->base) >> 3;
        return (nurs->mark_bits[slot >> 6] & (1ULL << (slot & 63u))) != 0;
    }

    gc_chunk_t *chunk = find_chunk(addr);
    if (chunk != NULL) {
        size_t pidx = (addr - chunk->base) >> GC_PAGE_SHIFT;
        if (pidx < chunk->first_data_page) return false;
        gc_page_t *page = &chunk->pages[pidx];
        if (page->state != GC_PAGE_INUSE) return false;
        uintptr_t hdr_addr = addr - Header_size;
        if (hdr_addr < page->base) return false;
        size_t off = hdr_addr - page->base;
        size_t slot_idx = off / page->slot_size;
        if (slot_idx * page->slot_size != off) return false;
        return (page->mark_bits[slot_idx >> 6] & (1ULL << (slot_idx & 63u))) != 0;
    }

    gc_large_t *lo = find_large_obj(addr);
    return (lo != NULL) ? lo->marked : false;
}

bool gc_mark_ptr(const void *payload_ptr)
{
    return mark_candidate_ptr((uintptr_t)payload_ptr);
}

GC_NO_SANITIZE_STACK static uintptr_t load_raw_stack_word(uintptr_t addr)
{
    return *(const uintptr_t *)addr;
}

static void mark_stack_range(uintptr_t sp_low, uintptr_t sp_high)
{
    size_t sp = 0;
    uintptr_t cur = sp_low & ~(uintptr_t)(WORD_SIZE - 1);
    for (; cur <= sp_high; cur += WORD_SIZE) {
        uintptr_t candidate = load_raw_stack_word(cur);
        if (candidate != 0) {
            try_mark_ptr_push(candidate, &sp);
        }
    }
    if (sp > 0) {
        drain_mark_stack(&sp);
    }
}

/* ---- Stop-The-World Collection (Sticky Minor GC or Full Major GC + Lazy Sweep) ---- */
static void gc_collect_locked(gc_thread_t *collector, bool force_major)
{
    _stw_in_progress = true;
    __atomic_store_n(&__gs_gc_stw_requested, 1, __ATOMIC_SEQ_CST);

    if (collector != NULL) {
        __atomic_store_n(&collector->state, THR_PARKED, __ATOMIC_SEQ_CST);
    }

    while (!all_threads_parked_locked()) {
        pthread_cond_wait(&_stw_park_cv, &_gc_mu);
    }

    /* Decide Minor vs Major GC */
    bool gen_enabled = __atomic_load_n(&_generational_enabled, __ATOMIC_RELAXED);
    bool is_major = force_major
                 || !gen_enabled
                 || (_major_collections == 0 && _minor_collections == 0)
                 || (_consecutive_minors >= MAX_CONSECUTIVE_MINORS)
                 || (_last_live_bytes >= _major_threshold_bytes)
                 || (_large_total_bytes >= _major_threshold_bytes);

    /* Retire all thread-local slab caches (pages remain linked in `_active_pages[c]`) */
    for (gc_thread_t *t = _threads_head; t != NULL; t = t->next) {
        for (size_t c = 0; c < GC_NUM_CLASSES; c++) {
            t->local_pages[c] = NULL;
        }
    }

    if (is_major) {
        /* Clear all mark_bits and reset live_count across all in-use pages & large objects */
        for (gc_chunk_t *ch = _chunks_head; ch != NULL; ch = ch->next) {
            for (size_t i = ch->first_data_page; i < GC_PAGES_PER_CHUNK; i++) {
                gc_page_t *p = &ch->pages[i];
                if (p->state == GC_PAGE_INUSE) {
                    memset(p->mark_bits, 0, sizeof(p->mark_bits));
                    p->live_count = 0;
                }
            }
        }
        for (gc_nursery_t *n = _nurseries_head; n != NULL; n = n->next) {
            memset(n->mark_bits, 0, sizeof(n->mark_bits));
            n->live_count = 0;
        }
        for (gc_large_t *lo = _large_head; lo != NULL; lo = lo->next) {
            lo->marked = false;
        }
        /* Clear all remembered bits & thread/orphan remsets */
        for (gc_thread_t *t = _threads_head; t != NULL; t = t->next) {
            for (size_t i = 0; i < t->remset_len; i++) {
                header_t *hp = (header_t *)(t->remset[i] - Header_size);
                __atomic_store_n(hp, __atomic_load_n(hp, __ATOMIC_RELAXED) & ~HEADER_REMEMBERED_BIT, __ATOMIC_RELAXED);
            }
            t->remset_len = 0;
        }
        for (size_t i = 0; i < _orphan_remset_len; i++) {
            header_t *hp = (header_t *)(_orphan_remset[i] - Header_size);
            __atomic_store_n(hp, __atomic_load_n(hp, __ATOMIC_RELAXED) & ~HEADER_REMEMBERED_BIT, __ATOMIC_RELAXED);
        }
        _orphan_remset_len = 0;
    }

    /* 1. Mark roots across all active registered threads (skip THR_IDLE foreign host threads) */
    for (gc_thread_t *t = _threads_head; t != NULL; t = t->next) {
        if (__atomic_load_n(&t->state, __ATOMIC_ACQUIRE) == THR_IDLE) {
            continue;
        }
        uintptr_t reg_base = (uintptr_t)&t->safepoint_regs;
        size_t reg_count = sizeof(jmp_buf) / sizeof(uintptr_t);
        size_t sp = 0;
        for (size_t i = 0; i < reg_count; i++) {
            uintptr_t rw = load_raw_stack_word(reg_base + i * sizeof(uintptr_t));
            if (rw != 0) {
                try_mark_ptr_push(rw, &sp);
            }
        }
        if (sp > 0) drain_mark_stack(&sp);

        if (t->safepoint_sp != 0 && t->root_start != 0) {
            uintptr_t lo = (t->safepoint_sp < t->root_start) ? t->safepoint_sp : t->root_start;
            uintptr_t hi = (t->safepoint_sp < t->root_start) ? t->root_start : t->safepoint_sp;
            mark_stack_range(lo, hi);
        }
    }

    /* 2. Mark registered global value slots */
    {
        size_t sp = 0;
        for (size_t i = 0; i < _global_roots_count; i++) {
            uintptr_t candidate = (uintptr_t)(*_global_roots[i]);
            if (candidate != 0) {
                try_mark_ptr_push(candidate, &sp);
            }
        }
        /* 2b. Mark pinned StableHandle table entries (both minor & major GC) */
        for (size_t i = 1; i <= _handle_used; i++) {
            uintptr_t candidate = (uintptr_t)_handle_slots[i];
            if (candidate != 0) {
                try_mark_ptr_push(candidate, &sp);
            }
        }
        if (sp > 0) drain_mark_stack(&sp);
    }

    /* 3. For Minor GC: trace remembered Old -> Young mutated containers and clear remsets */
    if (!is_major) {
        for (gc_thread_t *t = _threads_head; t != NULL; t = t->next) {
            for (size_t i = 0; i < t->remset_len; i++) {
                uintptr_t obj_ptr = t->remset[i];
                header_t *hp = (header_t *)(obj_ptr - Header_size);
                __atomic_store_n(hp, __atomic_load_n(hp, __ATOMIC_RELAXED) & ~HEADER_REMEMBERED_BIT, __ATOMIC_RELAXED);
                scan_object_children_only(obj_ptr);
            }
            t->remset_len = 0;
        }
        for (size_t i = 0; i < _orphan_remset_len; i++) {
            uintptr_t obj_ptr = _orphan_remset[i];
            header_t *hp = (header_t *)(obj_ptr - Header_size);
            __atomic_store_n(hp, __atomic_load_n(hp, __ATOMIC_RELAXED) & ~HEADER_REMEMBERED_BIT, __ATOMIC_RELAXED);
            scan_object_children_only(obj_ptr);
        }
        _orphan_remset_len = 0;
    }

    /* 4. Trace values held inside active/reachable Tasks, Channels, MVars, and Actors */
    gs_conc_mark_roots();

    /* 5. Reclaim unreachable synchronization handles */
    gs_conc_sweep_unreachable();

    /* 5b. Phase 1 Cleanup: detach unreachable cleanup entries (ZERO user calls during STW!) */
    {
        gc_cleanup_entry_t *e = _cleanup_active_head;
        while (e != NULL) {
            gc_cleanup_entry_t *next = e->next;
            if (!gc_is_obj_marked(e->owner)) {
                if (e->prev != NULL) e->prev->next = e->next;
                else _cleanup_active_head = e->next;
                if (e->next != NULL) e->next->prev = e->prev;
                if (_external_bytes_live >= e->external_bytes) {
                    _external_bytes_live -= e->external_bytes;
                } else {
                    _external_bytes_live = 0;
                }
                e->prev = NULL;
                e->next = NULL;
                if (_cleanup_pending_tail != NULL) {
                    _cleanup_pending_tail->next = e;
                    _cleanup_pending_tail = e;
                } else {
                    _cleanup_pending_head = e;
                    _cleanup_pending_tail = e;
                }
            }
            e = next;
        }
        _external_bytes_since_gc = 0;
        size_t next_ext = _external_bytes_live / 2u;
        if (next_ext < 64u * 1024u * 1024u) next_ext = 64u * 1024u * 1024u;
        _external_gc_threshold = next_ext;
    }

    /* 6. Reclassify slab pages (ZERO per-object sweep during STW!) & release empty pages to OS */
    size_t total_live_bytes = 0;
    for (size_t c = 0; c < GC_NUM_CLASSES; c++) {
        _unswept_pages[c] = NULL;
        _full_pages[c] = NULL;
        _active_pages[c] = NULL;
    }

    for (gc_chunk_t *ch = _chunks_head; ch != NULL; ch = ch->next) {
        for (size_t i = ch->first_data_page; i < GC_PAGES_PER_CHUNK; i++) {
            gc_page_t *p = &ch->pages[i];
            if (p->state != GC_PAGE_INUSE) continue;

            if (p->live_count == 0) {
                /* Entire 16 KB page is dead: return physical RAM to OS immediately! */
                p->state = GC_PAGE_FREE;
                p->free_list = NULL;
                p->bump_idx = 0;
                memset(p->alloc_bits, 0, sizeof(p->alloc_bits));
                memset(p->mark_bits, 0, sizeof(p->mark_bits));
                release_page_memory((void *)p->base, GC_PAGE_SIZE);
                page_list_push(&_free_pages, p, PAGE_LIST_FREE);
                _free_page_count++;
            } else {
                total_live_bytes += (size_t)p->live_count * p->slot_size;
                if (p->live_count < p->num_slots) {
                    page_list_push(&_unswept_pages[p->size_class], p, PAGE_LIST_UNSWEPT);
                } else {
                    page_list_push(&_full_pages[p->size_class], p, PAGE_LIST_FULL);
                }
            }
        }
    }

    /* 6b. Sweep & O(1)-reset bump-pointer nurseries; munmap dead retired nurseries */
    {
        gc_nursery_t *n = _nurseries_head;
        while (n != NULL) {
            gc_nursery_t *next = n->next;
            if (n->live_count == 0) {
                if (n->owned) {
                    /* All young objects in this nursery died: O(1) Arena reset! */
                    n->cur = n->base;
                    memset(n->alloc_bits, 0, sizeof(n->alloc_bits));
                    memset(n->mark_bits, 0, sizeof(n->mark_bits));
                } else {
                    if (n->prev != NULL) n->prev->next = n->next;
                    else _nurseries_head = n->next;
                    if (n->next != NULL) n->next->prev = n->prev;
                    nursery_table_remove_locked(n);
                    munmap((void *)n->base, GC_NURSERY_SIZE);
                    free(n);
                }
            } else {
                total_live_bytes += (size_t)n->live_count * 32u;
                if (n->owned && (n->end - n->cur) < 16384u) {
                    /* Detach nearly-full nursery with survivors so thread gets a fresh one */
                    for (gc_thread_t *t = _threads_head; t != NULL; t = t->next) {
                        if (t->nursery == n) {
                            t->nursery = NULL;
                        }
                    }
                    n->owned = false;
                }
                if (is_major && !n->owned) {
                    /* Release dead 16 KB pages inside retired nurseries back to OS (MADV_FREE_REUSABLE) */
                    size_t pages = GC_NURSERY_SIZE / GC_PAGE_SIZE;
                    size_t words_per_page = (GC_PAGE_SIZE >> 3) >> 6; /* 32 uint64_t words per 16 KB page */
                    for (size_t pg = 0; pg < pages; pg++) {
                        size_t base_w = pg * words_per_page;
                        uint64_t any_live = 0;
                        uint64_t any_alloc = 0;
                        for (size_t w = 0; w < words_per_page; w++) {
                            any_live |= n->mark_bits[base_w + w];
                            any_alloc |= n->alloc_bits[base_w + w];
                        }
                        bool prev_tail_live = (pg > 0) && (n->mark_bits[base_w - 1u] != 0);
                        if (any_live == 0 && any_alloc != 0 && !prev_tail_live) {
                            memset(&n->alloc_bits[base_w], 0, words_per_page * sizeof(uint64_t));
                            release_page_memory((void *)(n->base + pg * GC_PAGE_SIZE), GC_PAGE_SIZE);
                        }
                    }
                }
            }
            n = next;
        }
    }

    /* 6c. Reclaim completely empty 4 MB chunks back to OS on major GC */
    if (is_major) {
        reclaim_empty_chunks_locked(1);
    }

    /* 7. Sweep large objects (reuse <=256 KB blocks in cache or munmap back to OS!) */
    gc_large_t *lo = _large_head;
    while (lo != NULL) {
        gc_large_t *next = lo->next;
        if (lo->marked) {
            total_live_bytes += lo->map_size;
        } else {
            if (lo->prev != NULL) lo->prev->next = lo->next;
            else _large_head = lo->next;
            if (lo->next != NULL) lo->next->prev = lo->prev;
            large_table_remove_locked(lo);
            size_t msz = lo->map_size;
            if (_large_total_bytes >= msz) _large_total_bytes -= msz;
            else _large_total_bytes = 0;
            if (msz >= GC_PAGE_SIZE && msz <= LARGE_CACHE_MAX_BYTES &&
                _large_cache_bytes + msz <= _large_cache_limit_bytes) {
                size_t b = (msz >> GC_PAGE_SHIFT) - 1u;
                *(void **)lo = _large_cache_buckets[b];
                _large_cache_buckets[b] = (void *)lo;
                _large_cache_bytes += msz;
            } else {
                munmap(lo, msz);
            }
        }
        lo = next;
    }

    _gc_epoch++;
    _bytes_alloc_since_gc = 0;
    _last_live_bytes = total_live_bytes;

    size_t soft_headroom = 0;
    if (_soft_mem_limit_bytes > 0) {
        size_t budget = (_soft_mem_limit_bytes > total_live_bytes)
                      ? (_soft_mem_limit_bytes - total_live_bytes)
                      : 0u;
        soft_headroom = budget / 2u;
        size_t min_headroom = _soft_mem_limit_bytes / 8u;
        if (min_headroom > 2u * 1024u * 1024u) min_headroom = 2u * 1024u * 1024u;
        if (min_headroom < 256u * 1024u) min_headroom = 256u * 1024u;
        if (soft_headroom < min_headroom) soft_headroom = min_headroom;
    }

    if (is_major) {
        _major_collections++;
        _consecutive_minors = 0;
        _last_major_live_bytes = total_live_bytes;
        size_t next_major = total_live_bytes * 2u;
        if (_soft_mem_limit_bytes > 0) {
            size_t limited = total_live_bytes + soft_headroom;
            if (limited < next_major) next_major = limited;
        } else if (next_major < MIN_MAJOR_THRESHOLD_BYTES && _init_threshold_bytes >= MIN_GC_THRESHOLD_BYTES) {
            next_major = MIN_MAJOR_THRESHOLD_BYTES;
        } else if (next_major < _init_threshold_bytes * 4) {
            next_major = _init_threshold_bytes * 4;
        }
        _major_threshold_bytes = next_major;
    } else {
        _minor_collections++;
        _consecutive_minors++;
    }

    /* Adaptive next-GC threshold: at least `_init_threshold_bytes` (unless constrained by soft limit), scaling with live set */
    size_t next_thresh = is_major ? (total_live_bytes / 2) : (total_live_bytes / 4);
    if (next_thresh < _init_threshold_bytes) {
        next_thresh = _init_threshold_bytes;
    }
    /* Cap nursery budget at 16 MB for responsive Minor GC pauses */
    if (gen_enabled && !is_major && next_thresh > 16u * 1024u * 1024u) {
        next_thresh = 16u * 1024u * 1024u;
    }
    if (soft_headroom > 0 && next_thresh > soft_headroom) {
        next_thresh = soft_headroom;
    }
    _gc_threshold_bytes = next_thresh;

    if (collector != NULL) {
        __atomic_store_n(&collector->state, THR_RUNNING, __ATOMIC_SEQ_CST);
    }
    __atomic_store_n(&__gs_gc_stw_requested, 0, __ATOMIC_SEQ_CST);
    _stw_in_progress = false;
    pthread_cond_broadcast(&_stw_resume_cv);
}

void gc_collect_major(void)
{
    gc_thread_t *self = _tls_thread;
    jmp_buf regs;
    uintptr_t sp_here = current_stack_sp();
    _setjmp(regs);

    pthread_mutex_lock(&_gc_mu);
    if (self != NULL) {
        memcpy(&self->safepoint_regs, &regs, sizeof(jmp_buf));
        self->safepoint_sp = sp_here;
    }
    gc_collect_locked(self, true);
    pthread_mutex_unlock(&_gc_mu);
    gc_drain_cleanups_unlocked();
}

void geisha_rt_init(void)
{
    init_size_tables();
    size_t minor_b = 0, major_b = 0;
    compute_default_thresholds(131072u, &minor_b, &major_b);
    pthread_mutex_lock(&_gc_mu);
    if (!_gc_heap_inited) {
        if (!_thresholds_custom) {
            _init_threshold_bytes = minor_b;
            _gc_threshold_bytes = minor_b;
            _major_threshold_bytes = major_b;
        }
        if (_chunks_head == NULL) {
            if (!alloc_chunk_locked()) {
                pthread_mutex_unlock(&_gc_mu);
                fprintf(stderr, "GC initial chunk allocation failed\n");
                abort();
            }
        }
        __atomic_store_n(&_generational_enabled, true, __ATOMIC_RELEASE);
        _gc_heap_inited = true;
    }
    pthread_mutex_unlock(&_gc_mu);
}

static void host_thread_destructor(void *ptr)
{
    gc_thread_t *thr = (gc_thread_t *)ptr;
    if (thr != NULL) {
        _tls_thread = thr;
        gc_thread_detach();
    }
}

static void init_host_thr_key(void)
{
    pthread_key_create(&_host_thr_key, host_thread_destructor);
}

int64_t gc_host_enter(void *stack_anchor)
{
    gc_thread_t *self = _tls_thread;
    if (__builtin_expect(self != NULL, 1)) {
        int32_t prev = __atomic_load_n(&self->state, __ATOMIC_ACQUIRE);
        if (prev == THR_IDLE) {
            if (__builtin_expect(__atomic_load_n(&__gs_gc_stw_requested, __ATOMIC_SEQ_CST) != 0, 0)) {
                pthread_mutex_lock(&_gc_mu);
                while (_stw_in_progress) {
                    pthread_cond_wait(&_stw_resume_cv, &_gc_mu);
                }
                self->root_start = (uintptr_t)stack_anchor;
                __atomic_store_n(&self->state, THR_RUNNING, __ATOMIC_SEQ_CST);
                pthread_mutex_unlock(&_gc_mu);
                return 3;
            }
            self->root_start = (uintptr_t)stack_anchor;
            __atomic_store_n(&self->state, THR_RUNNING, __ATOMIC_SEQ_CST);
            if (__builtin_expect(__atomic_load_n(&__gs_gc_stw_requested, __ATOMIC_SEQ_CST) != 0, 0)) {
                gc_safepoint_slow();
            }
            return 3;
        }
        if (prev == THR_BLOCKED) {
            gc_leave_blocking();
            return 2;
        }
        return 1;
    }
    pthread_once(&_host_key_once, init_host_thr_key);
    geisha_rt_init();
    gc_thread_attach(stack_anchor);
    pthread_setspecific(_host_thr_key, _tls_thread);
    return 3;
}

void gc_host_leave(int64_t token)
{
    if (__builtin_expect(token == 3, 1)) {
        gc_thread_t *self = _tls_thread;
        if (self != NULL) {
            self->root_start = 0;
            self->safepoint_sp = 0;
            __atomic_store_n(&self->state, THR_IDLE, __ATOMIC_SEQ_CST);
            if (__builtin_expect(__atomic_load_n(&__gs_gc_stw_requested, __ATOMIC_ACQUIRE) != 0, 0)) {
                pthread_mutex_lock(&_gc_mu);
                if (_stw_in_progress && all_threads_parked_locked()) {
                    pthread_cond_signal(&_stw_park_cv);
                }
                pthread_mutex_unlock(&_gc_mu);
            }
        }
    } else if (token == 0) {
        gc_thread_detach();
    } else if (token == 2) {
        gc_thread_t *self = _tls_thread;
        if (self != NULL) {
            __atomic_store_n(&self->state, THR_BLOCKED, __ATOMIC_RELEASE);
        }
    }
}

int64_t gc_handle_new(void *obj)
{
    if (obj == NULL) return 0;
    pthread_mutex_lock(&_gc_mu);
    size_t idx = 0;
    if (_handle_free_len > 0) {
        idx = _handle_free[--_handle_free_len];
    } else {
        size_t next = _handle_used + 1;
        if (next >= _handle_cap) {
            size_t ncap = (_handle_cap == 0) ? 64u : (_handle_cap * 2u);
            while (ncap <= next) ncap *= 2u;
            void **ns = (void **)realloc(_handle_slots, ncap * sizeof(void *));
            if (ns == NULL) {
                pthread_mutex_unlock(&_gc_mu);
                abort();
            }
            if (_handle_cap == 0) ns[0] = NULL;
            _handle_slots = ns;
            _handle_cap = ncap;
        }
        _handle_used = next;
        idx = next;
    }
    _handle_slots[idx] = obj;
    pthread_mutex_unlock(&_gc_mu);
    return (int64_t)idx;
}

void *gc_handle_get(int64_t handle)
{
    if (handle <= 0) return NULL;
    pthread_mutex_lock(&_gc_mu);
    void *res = NULL;
    if ((size_t)handle <= _handle_used) {
        res = _handle_slots[(size_t)handle];
    }
    pthread_mutex_unlock(&_gc_mu);
    return res;
}

void gc_handle_free(int64_t handle)
{
    if (handle <= 0) return;
    pthread_mutex_lock(&_gc_mu);
    if ((size_t)handle <= _handle_used && _handle_slots[(size_t)handle] != NULL) {
        _handle_slots[(size_t)handle] = NULL;
        if (_handle_free_len >= _handle_free_cap) {
            size_t ncap = (_handle_free_cap == 0) ? 64u : (_handle_free_cap * 2u);
            size_t *nf = (size_t *)realloc(_handle_free, ncap * sizeof(size_t));
            if (nf == NULL) {
                pthread_mutex_unlock(&_gc_mu);
                abort();
            }
            _handle_free = nf;
            _handle_free_cap = ncap;
        }
        _handle_free[_handle_free_len++] = (size_t)handle;
    }
    pthread_mutex_unlock(&_gc_mu);
}

void gc_set_thresholds(size_t minor_bytes, size_t major_bytes)
{
    if (minor_bytes < 64u * 1024u) minor_bytes = 64u * 1024u;
    if (major_bytes < minor_bytes * 2u) major_bytes = minor_bytes * 2u;
    pthread_mutex_lock(&_gc_mu);
    _init_threshold_bytes = minor_bytes;
    _gc_threshold_bytes = minor_bytes;
    _major_threshold_bytes = major_bytes;
    _thresholds_custom = true;
    pthread_mutex_unlock(&_gc_mu);
}

void gc_set_mem_limit(size_t soft_limit_bytes)
{
    pthread_mutex_lock(&_gc_mu);
    _soft_mem_limit_bytes = soft_limit_bytes;
    if (soft_limit_bytes == 0) {
        _large_cache_limit_bytes = LARGE_CACHE_DEFAULT_TOTAL_BYTES;
    } else {
        size_t cache_cap = soft_limit_bytes / 16u;
        if (cache_cap < 1024u * 1024u) cache_cap = 1024u * 1024u;
        if (cache_cap > LARGE_CACHE_DEFAULT_TOTAL_BYTES) cache_cap = LARGE_CACHE_DEFAULT_TOTAL_BYTES;
        _large_cache_limit_bytes = cache_cap;
        if (_large_cache_bytes > _large_cache_limit_bytes) {
            drain_large_cache_locked();
        }
    }
    pthread_mutex_unlock(&_gc_mu);
}

void gc_trim(void)
{
    geisha_rt_init();
    gc_collect_major();
    pthread_mutex_lock(&_gc_mu);
    drain_large_cache_locked();
    reclaim_empty_chunks_locked(1);
    for (gc_page_t *p = _free_pages; p != NULL; p = p->next) {
        release_page_memory((void *)p->base, GC_PAGE_SIZE);
    }
    pthread_mutex_unlock(&_gc_mu);
}

/* ============================================================================
 * Two-Phase GC Cleanup, ForeignPtr & Scoped Bump-Pointer Arena
 * ============================================================================ */

int64_t gc_cleanup_register(void *owner, gc_cleanup_fn fn, void *arg, size_t external_bytes)
{
    if (owner == NULL || fn == NULL) return 0;
    gc_cleanup_entry_t *e = (gc_cleanup_entry_t *)malloc(sizeof(gc_cleanup_entry_t));
    if (e == NULL) abort();

    bool trigger_gc = false;
    pthread_mutex_lock(&_gc_mu);
    int64_t tok = _cleanup_next_token++;
    e->token = tok;
    e->owner = owner;
    e->fn = fn;
    e->arg = arg;
    e->external_bytes = external_bytes;
    e->prev = NULL;
    e->next = _cleanup_active_head;
    if (_cleanup_active_head != NULL) {
        _cleanup_active_head->prev = e;
    }
    _cleanup_active_head = e;
    _external_bytes_live += external_bytes;
    _external_bytes_since_gc += external_bytes;
    if (_external_bytes_since_gc >= _external_gc_threshold && !_stw_in_progress) {
        trigger_gc = true;
    }
    pthread_mutex_unlock(&_gc_mu);

    if (trigger_gc) {
        volatile void *keep_owner = owner;
        gc_collect_major();
        (void)keep_owner;
    }
    return tok;
}

bool gc_cleanup_cancel(int64_t token)
{
    if (token <= 0) return false;
    gc_cleanup_entry_t *found = NULL;
    pthread_mutex_lock(&_gc_mu);
    for (gc_cleanup_entry_t *e = _cleanup_active_head; e != NULL; e = e->next) {
        if (e->token == token) {
            if (e->prev != NULL) e->prev->next = e->next;
            else _cleanup_active_head = e->next;
            if (e->next != NULL) e->next->prev = e->prev;
            if (_external_bytes_live >= e->external_bytes) {
                _external_bytes_live -= e->external_bytes;
            } else {
                _external_bytes_live = 0;
            }
            found = e;
            break;
        }
    }
    pthread_mutex_unlock(&_gc_mu);
    if (found != NULL) {
        free(found);
        return true;
    }
    return false;
}

size_t gc_external_live_bytes(void)
{
    pthread_mutex_lock(&_gc_mu);
    size_t v = _external_bytes_live;
    pthread_mutex_unlock(&_gc_mu);
    return v;
}

typedef struct {
    void *raw_ptr;
    int64_t token;
} gc_foreign_ptr_t;

void *gc_foreign_ptr_new(void *raw_ptr, gc_cleanup_fn fn, size_t external_bytes)
{
    gc_foreign_ptr_t *fp = (gc_foreign_ptr_t *)gc_alloc_atomic(sizeof(gc_foreign_ptr_t));
    fp->raw_ptr = raw_ptr;
    fp->token = 0;
    if (fn != NULL && raw_ptr != NULL) {
        fp->token = gc_cleanup_register((void *)fp, fn, raw_ptr, external_bytes);
    }
    return (void *)fp;
}

void *gc_foreign_ptr_alloc(int64_t size_bytes)
{
    if (size_bytes <= 0) size_bytes = 1;
    void *raw = NULL;
    size_t n = ((size_t)size_bytes + 63u) & ~(size_t)63u;
    if (posix_memalign(&raw, 64u, n) != 0 || raw == NULL) abort();
    memset(raw, 0, n);
    return gc_foreign_ptr_new(raw, free, n);
}

void *gc_foreign_ptr_get(void *fp_void)
{
    if (fp_void == NULL) return NULL;
    gc_foreign_ptr_t *fp = (gc_foreign_ptr_t *)fp_void;
    return fp->raw_ptr;
}

/* Scoped Bump-Pointer Arena (NoScan raw bytes, 64-byte SIMD-aligned allocations) */
#define ARENA_DEFAULT_BLOCK_SIZE (64u * 1024u)

typedef struct gc_arena_block_t {
    struct gc_arena_block_t *next;
    size_t cap;
    size_t used;
    unsigned char data[];
} gc_arena_block_t;

typedef struct {
    gc_arena_block_t *head;
} gc_arena_t;

void *gc_arena_new(void)
{
    gc_arena_t *a = (gc_arena_t *)malloc(sizeof(gc_arena_t));
    if (a == NULL) abort();
    a->head = NULL;
    return (void *)a;
}

void *gc_arena_alloc(void *arena_void, int64_t size_bytes)
{
    if (arena_void == NULL || size_bytes <= 0) return NULL;
    gc_arena_t *a = (gc_arena_t *)arena_void;
    size_t n = ((size_t)size_bytes + 63u) & ~(size_t)63u;
    gc_arena_block_t *b = a->head;
    if (b == NULL || b->used + n > b->cap) {
        size_t blk_cap = (n > ARENA_DEFAULT_BLOCK_SIZE) ? n : ARENA_DEFAULT_BLOCK_SIZE;
        size_t hdr_sz = (sizeof(gc_arena_block_t) + 63u) & ~(size_t)63u;
        unsigned char *raw = NULL;
        if (posix_memalign((void **)&raw, 64u, hdr_sz + blk_cap) != 0 || raw == NULL) {
            abort();
        }
        b = (gc_arena_block_t *)raw;
        b->next = a->head;
        b->cap = blk_cap;
        b->used = 0;
        a->head = b;
    }
    size_t hdr_sz = (sizeof(gc_arena_block_t) + 63u) & ~(size_t)63u;
    void *ptr = (unsigned char *)b + hdr_sz + b->used;
    b->used += n;
    return ptr;
}

void gc_arena_destroy(void *arena_void)
{
    if (arena_void == NULL) return;
    gc_arena_t *a = (gc_arena_t *)arena_void;
    gc_arena_block_t *b = a->head;
    while (b != NULL) {
        gc_arena_block_t *next = b->next;
        free(b);
        b = next;
    }
    free(a);
}
