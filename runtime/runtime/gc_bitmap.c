#include "../include/gc_bitmap.h"
#include "../include/gs_conc.h"

#include <pthread.h>
#include <setjmp.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAX_GLOBAL_ROOTS 4096
#define NUM_FREE_BINS 16
#define TLAB_TARGET_WORDS 4096
#define TLAB_MAX_OBJ_WORDS 64

/* Global safepoint flag polled by generated LLVM IR (`0` = normal execution, `1` = STW requested) */
int32_t __gs_gc_stw_requested = 0;

typedef struct gc_thread_t {
    uintptr_t root_start;
    uintptr_t safepoint_sp;
    jmp_buf safepoint_regs;
    bool is_blocked_or_parked;
    /* Thread-local bump-pointer allocation buffer (64-word bitmap-aligned, lock-free fast path) */
    uintptr_t tlab_cur;
    uintptr_t tlab_end;
    gc_heap_t *tlab_heap;
    struct gc_thread_t *next;
    struct gc_thread_t *prev;
} gc_thread_t;

static pthread_mutex_t _gc_mu = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t _stw_park_cv = PTHREAD_COND_INITIALIZER;
static pthread_cond_t _stw_resume_cv = PTHREAD_COND_INITIALIZER;
static bool _stw_in_progress = false;

static _Thread_local gc_thread_t *_tls_thread = NULL;
static gc_thread_t *_threads_head = NULL;

static gc_heap_t *_heaps = NULL;
static uintptr_t _min_heap_addr = UINTPTR_MAX;
static uintptr_t _max_heap_addr = 0;

/* Size-segregated free lists: bin b holds blocks of size [2^(b+1), 2^(b+2)-1] words */
static gc_free_t *_free_bins[NUM_FREE_BINS];
static uint32_t _free_bin_mask = 0;

static size_t _default_init_words = 131072;
static size_t _last_sweep_total_words = 0;
static size_t _last_sweep_free_words = 0;
static void **_global_roots[MAX_GLOBAL_ROOTS];
static size_t _global_roots_count = 0;
static size_t _collections = 0;

static gc_heap_t *new_heap(size_t words);
static void *pickup_fragment(size_t size_words, size_t *out_total_words);
static void bitmap_collect_locked(gc_thread_t *collector);
static void bitmap_mark_stack_range(uintptr_t sp_low, uintptr_t sp_high);
static bool bitmap_mark_obj(gc_heap_t *heap, uintptr_t hdr_addr);
static void bitmap_sweep(void);
static gc_heap_t *find_allocated_object_heap(uintptr_t payload_ptr);

static inline unsigned free_bin_index(size_t words)
{
    if (words < 4) return 0;
    unsigned lz = (unsigned)__builtin_clzll((unsigned long long)words);
    unsigned b = (63u - lz) - 1u;
    return (b >= NUM_FREE_BINS) ? (NUM_FREE_BINS - 1u) : b;
}

static inline void free_list_clear(void)
{
    memset(_free_bins, 0, sizeof(_free_bins));
    _free_bin_mask = 0;
}

static inline void free_list_insert(uintptr_t addr, size_t words)
{
    if (words < 2) return;
    unsigned b = free_bin_index(words);
    gc_free_t *frag = (gc_free_t *)addr;
    frag->size = words;
    frag->next = _free_bins[b];
    _free_bins[b] = frag;
    _free_bin_mask |= (1u << b);
}

static inline gc_heap_t *find_heap_for_addr(uintptr_t addr)
{
    for (gc_heap_t *h = _heaps; h != NULL; h = h->next) {
        if (addr >= h->base && addr < h->end) {
            return h;
        }
    }
    return NULL;
}

static inline void register_heap_bounds(gc_heap_t *h)
{
    if (h->base < _min_heap_addr) _min_heap_addr = h->base;
    if (h->end > _max_heap_addr) _max_heap_addr = h->end;
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

static bool all_threads_parked_locked(void)
{
    for (gc_thread_t *t = _threads_head; t != NULL; t = t->next) {
        if (!t->is_blocked_or_parked) {
            return false;
        }
    }
    return true;
}

size_t gc_collection_count(void)
{
    pthread_mutex_lock(&_gc_mu);
    size_t c = _collections;
    pthread_mutex_unlock(&_gc_mu);
    return c;
}

void gc_register_root(void **slot)
{
    if (slot == NULL) return;
    pthread_mutex_lock(&_gc_mu);
    if (_global_roots_count < MAX_GLOBAL_ROOTS) {
        _global_roots[_global_roots_count++] = slot;
    }
    pthread_mutex_unlock(&_gc_mu);
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

void gc_init_with_stack(size_t init_size_words, void *stack_anchor)
{
    const char *env_words = getenv("GEISHA_GC_HEAP_WORDS");
    if (env_words != NULL) {
        long parsed = atol(env_words);
        if (parsed >= 32) {
            init_size_words = (size_t)parsed;
        }
    }
    if (init_size_words < 32) {
        init_size_words = 32;
    }

    pthread_mutex_lock(&_gc_mu);
    _default_init_words = init_size_words;
    _heaps = new_heap(init_size_words);
    if (_heaps == NULL) {
        pthread_mutex_unlock(&_gc_mu);
        fprintf(stderr, "GC initial heap allocation failed\n");
        abort();
    }
    _min_heap_addr = _heaps->base;
    _max_heap_addr = _heaps->end;

    free_list_clear();
    free_list_insert(_heaps->base, _heaps->total_words);

    _global_roots_count = 0;
    _collections = 0;
    _stw_in_progress = false;
    __atomic_store_n(&__gs_gc_stw_requested, 0, __ATOMIC_RELEASE);

    if (_tls_thread == NULL) {
        gc_thread_t *main_thr = (gc_thread_t *)calloc(1, sizeof(gc_thread_t));
        if (main_thr == NULL) {
            pthread_mutex_unlock(&_gc_mu);
            abort();
        }
        main_thr->root_start = (uintptr_t)stack_anchor;
        main_thr->is_blocked_or_parked = false;
        link_thread_locked(main_thr);
        _tls_thread = main_thr;
    } else {
        _tls_thread->root_start = (uintptr_t)stack_anchor;
        _tls_thread->is_blocked_or_parked = false;
        _tls_thread->tlab_cur = 0;
        _tls_thread->tlab_end = 0;
        _tls_thread->tlab_heap = NULL;
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
    thr->is_blocked_or_parked = false;

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
    unlink_thread_locked(thr);
    if (_stw_in_progress && all_threads_parked_locked()) {
        pthread_cond_signal(&_stw_park_cv);
    }
    pthread_mutex_unlock(&_gc_mu);
    _tls_thread = NULL;
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
    volatile uintptr_t sp_marker = 0;

    pthread_mutex_lock(&_gc_mu);
    if (_stw_in_progress) {
        memcpy(&self->safepoint_regs, &regs, sizeof(jmp_buf));
        self->safepoint_sp = (uintptr_t)&sp_marker;
        self->is_blocked_or_parked = true;
        if (all_threads_parked_locked()) {
            pthread_cond_signal(&_stw_park_cv);
        }
        while (_stw_in_progress) {
            pthread_cond_wait(&_stw_resume_cv, &_gc_mu);
        }
        self->is_blocked_or_parked = false;
    }
    pthread_mutex_unlock(&_gc_mu);
}

void gc_enter_blocking(void *jmp_buf_on_stack)
{
    gc_thread_t *self = _tls_thread;
    if (self == NULL) {
        return;
    }
    volatile uintptr_t sp_here = 0;

    pthread_mutex_lock(&_gc_mu);
    if (jmp_buf_on_stack != NULL) {
        memcpy(&self->safepoint_regs, jmp_buf_on_stack, sizeof(jmp_buf));
        self->safepoint_sp = (uintptr_t)jmp_buf_on_stack;
    } else {
        self->safepoint_sp = (uintptr_t)&sp_here;
    }
    self->is_blocked_or_parked = true;
    if (_stw_in_progress && all_threads_parked_locked()) {
        pthread_cond_signal(&_stw_park_cv);
    }
    pthread_mutex_unlock(&_gc_mu);
}

void gc_leave_blocking(void)
{
    gc_thread_t *self = _tls_thread;
    if (self == NULL) {
        return;
    }
    pthread_mutex_lock(&_gc_mu);
    while (_stw_in_progress) {
        pthread_cond_wait(&_stw_resume_cv, &_gc_mu);
    }
    self->is_blocked_or_parked = false;
    pthread_mutex_unlock(&_gc_mu);
}

static gc_heap_t *new_heap(size_t max_size_words)
{
    /* Each free fragment needs at least 2 words (`size` + `next`) */
    if (max_size_words < 64) {
        max_size_words = 64;
    }
    if (max_size_words % BITS_PER_BITMAP != 0) {
        max_size_words = ((max_size_words / BITS_PER_BITMAP) + 1) * BITS_PER_BITMAP;
    }

    size_t bitslen = max_size_words / BITS_PER_BITMAP;

    gc_heap_t *h = (gc_heap_t *)calloc(1, sizeof(gc_heap_t));
    if (h == NULL) return NULL;

    void *raw_mem = calloc(max_size_words, WORD_SIZE);
    bitmap_t *alloc_bits = (bitmap_t *)calloc(bitslen, sizeof(bitmap_t));
    bitmap_t *mark_bits = (bitmap_t *)calloc(bitslen, sizeof(bitmap_t));

    if (raw_mem == NULL || alloc_bits == NULL || mark_bits == NULL) {
        free(raw_mem);
        free(alloc_bits);
        free(mark_bits);
        free(h);
        return NULL;
    }

    h->base = (uintptr_t)raw_mem;
    h->end = h->base + max_size_words * WORD_SIZE;
    h->total_words = max_size_words;
    h->bitslen = bitslen;
    h->alloc_bits = alloc_bits;
    h->mark_bits = mark_bits;
    h->next = NULL;
    return h;
}

/* Carve a 64-word bitmap-aligned TLAB from free bins so its `alloc_bits` words are thread-exclusive */
static bool refill_tlab_locked(gc_thread_t *self, size_t min_words)
{
    size_t min_aligned = (min_words + (BITS_PER_BITMAP - 1)) & ~(size_t)(BITS_PER_BITMAP - 1);
    size_t need_min = min_aligned + (BITS_PER_BITMAP - 1);
    unsigned start_bin = free_bin_index(need_min);

    /* Prefer a large bin (TLAB_TARGET_WORDS) first so refills are infrequent */
    unsigned target_bin = free_bin_index(TLAB_TARGET_WORDS + BITS_PER_BITMAP);
    uint32_t hi_mask = _free_bin_mask & (~0u << target_bin);
    unsigned chosen_bin;
    if (hi_mask != 0) {
        chosen_bin = (unsigned)__builtin_ctz(hi_mask);
    } else {
        uint32_t avail = _free_bin_mask & (~0u << start_bin);
        if (avail == 0) return false;
        chosen_bin = (unsigned)__builtin_ctz(avail);
    }

    /* Try exact or larger bin */
    for (unsigned b = chosen_bin; b < NUM_FREE_BINS; b++) {
        if ((_free_bin_mask & (1u << b)) == 0) continue;
        gc_free_t **prev = &_free_bins[b];
        gc_free_t *cur = _free_bins[b];
        int steps = 0;
        while (cur != NULL && steps < 8) {
            if (cur->size >= min_aligned) {
                uintptr_t blk = (uintptr_t)cur;
                size_t blk_words = cur->size;
                gc_heap_t *h = find_heap_for_addr(blk);
                if (h != NULL) {
                    size_t off_words = (blk - h->base) / WORD_SIZE;
                    size_t aligned_off = (off_words + (BITS_PER_BITMAP - 1)) & ~(size_t)(BITS_PER_BITMAP - 1);
                    size_t lead = aligned_off - off_words;
                    if (blk_words >= lead + min_aligned) {
                        size_t avail_aligned = (blk_words - lead) & ~(size_t)(BITS_PER_BITMAP - 1);
                        size_t take_words = (avail_aligned > TLAB_TARGET_WORDS) ? TLAB_TARGET_WORDS : avail_aligned;
                        if (take_words < min_aligned) take_words = min_aligned;

                        /* Unlink `cur` */
                        *prev = cur->next;
                        if (_free_bins[b] == NULL) {
                            _free_bin_mask &= ~(1u << b);
                        }

                        /* Return unaligned leading/trailing fragments to free bins */
                        if (lead >= 2) {
                            free_list_insert(blk, lead);
                        }
                        size_t tail_words = blk_words - lead - take_words;
                        if (tail_words >= 2) {
                            free_list_insert(h->base + (aligned_off + take_words) * WORD_SIZE, tail_words);
                        }

                        self->tlab_heap = h;
                        self->tlab_cur = h->base + aligned_off * WORD_SIZE;
                        self->tlab_end = self->tlab_cur + take_words * WORD_SIZE;
                        return true;
                    }
                }
            }
            prev = &cur->next;
            cur = cur->next;
            steps++;
        }
    }
    return false;
}

__attribute__((noinline)) static void *gc_alloc_slow(size_t size_bytes, size_t payload_words, size_t total_words, bool noscan)
{
    gc_thread_t *self = _tls_thread;
    jmp_buf regs;
    bool regs_saved = false;
    volatile uintptr_t sp_marker = 0;

    pthread_mutex_lock(&_gc_mu);
    while (_stw_in_progress) {
        if (self != NULL) {
            if (!regs_saved) {
                _setjmp(regs);
                regs_saved = true;
            }
            memcpy(&self->safepoint_regs, &regs, sizeof(jmp_buf));
            self->safepoint_sp = (uintptr_t)&sp_marker;
            self->is_blocked_or_parked = true;
            if (all_threads_parked_locked()) {
                pthread_cond_signal(&_stw_park_cv);
            }
        }
        pthread_cond_wait(&_stw_resume_cv, &_gc_mu);
        if (self != NULL) {
            self->is_blocked_or_parked = false;
        }
    }

    /* Try TLAB refill first for small allocations */
    if (self != NULL && total_words <= TLAB_MAX_OBJ_WORDS) {
        if (refill_tlab_locked(self, total_words)) {
            header_t *hdr = (header_t *)self->tlab_cur;
            self->tlab_cur += total_words * WORD_SIZE;
            *hdr = (((header_t)payload_words) << 1) | (noscan ? HEADER_NOSCAN_BIT : (header_t)0);
            uintptr_t off = (uintptr_t)hdr - self->tlab_heap->base;
            self->tlab_heap->alloc_bits[OFFSET_TO_IDX(off)] |= OFFSET_TO_MASK(off);
            pthread_mutex_unlock(&_gc_mu);

            void *payload = (void *)(hdr + 1);
            zero_payload_words(payload, payload_words);
            return payload;
        }
    }

    size_t actual_total_words = total_words;
    void *block = pickup_fragment(total_words, &actual_total_words);
    bool collected = false;
    if (block == NULL) {
        if (self != NULL) {
            if (!regs_saved) {
                _setjmp(regs);
                regs_saved = true;
            }
            memcpy(&self->safepoint_regs, &regs, sizeof(jmp_buf));
            self->safepoint_sp = (uintptr_t)&sp_marker;
        }
        bitmap_collect_locked(self);
        collected = true;
        block = pickup_fragment(total_words, &actual_total_words);
    }

    /* Grow heap if allocation still failed OR post-GC free headroom is below 40% (prevents GC thrashing!) */
    if (block == NULL || (collected && _last_sweep_free_words * 5 < _last_sweep_total_words * 2)) {
        size_t total_cur = _last_sweep_total_words > 0 ? _last_sweep_total_words : (_heaps ? _heaps->total_words : _default_init_words);
        size_t grow_words = total_cur;
        if (grow_words < total_words * 2) {
            grow_words = total_words * 2;
        }
        gc_heap_t *extra = new_heap(grow_words);
        if (extra == NULL && block == NULL) {
            pthread_mutex_unlock(&_gc_mu);
            fprintf(stderr, "GC out of memory allocating %zu bytes\n", size_bytes);
            abort();
        }
        if (extra != NULL) {
            extra->next = _heaps;
            _heaps = extra;
            register_heap_bounds(extra);
            free_list_insert(extra->base, extra->total_words);
        }

        if (block == NULL) {
            block = pickup_fragment(total_words, &actual_total_words);
            if (block == NULL) {
                pthread_mutex_unlock(&_gc_mu);
                fprintf(stderr, "GC internal fragmentation failure\n");
                abort();
            }
        }
    }

    payload_words = actual_total_words - 1;

    header_t *hdr = (header_t *)block;
    *hdr = (((header_t)payload_words) << 1) | (noscan ? HEADER_NOSCAN_BIT : (header_t)0);

    uintptr_t hdr_addr = (uintptr_t)hdr;
    gc_heap_t *h = find_heap_for_addr(hdr_addr);
    if (h != NULL) {
        uintptr_t off = hdr_addr - h->base;
        h->alloc_bits[OFFSET_TO_IDX(off)] |= OFFSET_TO_MASK(off);
    }
    pthread_mutex_unlock(&_gc_mu);

    void *payload = (void *)(hdr + 1);
    zero_payload_words(payload, payload_words);
    return payload;
}

static inline void *gc_alloc_fast(size_t size_bytes, bool noscan)
{
    size_t payload_words = (size_bytes + WORD_SIZE - 1) / WORD_SIZE;
    if (payload_words == 0) {
        payload_words = 1;
    }
    size_t total_words = payload_words + 1; /* +1 word for object header */

    gc_thread_t *self = _tls_thread;
    if (__builtin_expect(
            self != NULL &&
            __atomic_load_n(&__gs_gc_stw_requested, __ATOMIC_RELAXED) == 0 &&
            total_words <= TLAB_MAX_OBJ_WORDS &&
            self->tlab_cur + total_words * WORD_SIZE <= self->tlab_end,
            1)) {
        header_t *hdr = (header_t *)self->tlab_cur;
        self->tlab_cur += total_words * WORD_SIZE;
        *hdr = (((header_t)payload_words) << 1) | (noscan ? HEADER_NOSCAN_BIT : (header_t)0);
        uintptr_t off = (uintptr_t)hdr - self->tlab_heap->base;
        self->tlab_heap->alloc_bits[OFFSET_TO_IDX(off)] |= OFFSET_TO_MASK(off);

        void *payload = (void *)(hdr + 1);
        zero_payload_words(payload, payload_words);
        return payload;
    }

    return gc_alloc_slow(size_bytes, payload_words, total_words, noscan);
}

void *gc_alloc(size_t size_bytes)
{
    return gc_alloc_fast(size_bytes, false);
}

void *gc_alloc_atomic(size_t size_bytes)
{
    return gc_alloc_fast(size_bytes, true);
}

static void *pickup_fragment(size_t size_words, size_t *out_total_words)
{
    unsigned b0 = free_bin_index(size_words);

    /* 1. Try the exact size bin first (bounded scan to stay O(1)) */
    if (_free_bin_mask & (1u << b0)) {
        gc_free_t **prev = &_free_bins[b0];
        gc_free_t *cur = _free_bins[b0];
        int steps = 0;
        while (cur != NULL && steps < 16) {
            if (cur->size >= size_words) {
                size_t rem = cur->size - size_words;
                *prev = cur->next;
                if (_free_bins[b0] == NULL) {
                    _free_bin_mask &= ~(1u << b0);
                }
                if (rem >= 2) {
                    free_list_insert((uintptr_t)cur + size_words * WORD_SIZE, rem);
                    *out_total_words = size_words;
                } else {
                    *out_total_words = cur->size;
                }
                return (void *)cur;
            }
            prev = &cur->next;
            cur = cur->next;
            steps++;
        }
    }

    /* 2. O(1) pop from the smallest strictly larger non-empty bin (guaranteed cur->size >= size_words) */
    if (b0 + 1 < NUM_FREE_BINS) {
        uint32_t larger_mask = _free_bin_mask & (~0u << (b0 + 1));
        if (larger_mask != 0) {
            unsigned b = (unsigned)__builtin_ctz(larger_mask);
            gc_free_t *cur = _free_bins[b];
            _free_bins[b] = cur->next;
            if (_free_bins[b] == NULL) {
                _free_bin_mask &= ~(1u << b);
            }
            size_t rem = cur->size - size_words;
            if (rem >= 2) {
                free_list_insert((uintptr_t)cur + size_words * WORD_SIZE, rem);
                *out_total_words = size_words;
            } else {
                *out_total_words = cur->size;
            }
            return (void *)cur;
        }
    }

    /* 3. Fallback: full scan of b0 if it had >16 entries and no larger bin was non-empty */
    if (_free_bin_mask & (1u << b0)) {
        gc_free_t **prev = &_free_bins[b0];
        gc_free_t *cur = _free_bins[b0];
        while (cur != NULL) {
            if (cur->size >= size_words) {
                size_t rem = cur->size - size_words;
                *prev = cur->next;
                if (_free_bins[b0] == NULL) {
                    _free_bin_mask &= ~(1u << b0);
                }
                if (rem >= 2) {
                    free_list_insert((uintptr_t)cur + size_words * WORD_SIZE, rem);
                    *out_total_words = size_words;
                } else {
                    *out_total_words = cur->size;
                }
                return (void *)cur;
            }
            prev = &cur->next;
            cur = cur->next;
        }
    }

    return NULL;
}

bool gc_is_obj_marked(const void *payload_ptr)
{
    uintptr_t addr = (uintptr_t)payload_ptr;
    gc_heap_t *h = find_allocated_object_heap(addr);
    if (h == NULL) {
        return false;
    }
    uintptr_t hdr_addr = addr - Header_size;
    uintptr_t off = hdr_addr - h->base;
    return (h->mark_bits[OFFSET_TO_IDX(off)] & OFFSET_TO_MASK(off)) != 0;
}

bool gc_mark_ptr(const void *payload_ptr)
{
    uintptr_t addr = (uintptr_t)payload_ptr;
    gc_heap_t *h = find_allocated_object_heap(addr);
    if (h == NULL) {
        return false;
    }
    return bitmap_mark_obj(h, addr - Header_size);
}

static void bitmap_collect_locked(gc_thread_t *collector)
{
    _stw_in_progress = true;
    __atomic_store_n(&__gs_gc_stw_requested, 1, __ATOMIC_RELEASE);

    if (collector != NULL) {
        collector->is_blocked_or_parked = true;
    }

    while (!all_threads_parked_locked()) {
        pthread_cond_wait(&_stw_park_cv, &_gc_mu);
    }

    /* Retire all active TLABs before sweeping (unused TLAB tails have alloc_bits == 0) */
    for (gc_thread_t *t = _threads_head; t != NULL; t = t->next) {
        t->tlab_cur = 0;
        t->tlab_end = 0;
        t->tlab_heap = NULL;
    }

    /* 1. Mark roots across all registered threads (saved registers + stack ranges) */
    for (gc_thread_t *t = _threads_head; t != NULL; t = t->next) {
        const uintptr_t *reg_words = (const uintptr_t *)&t->safepoint_regs;
        size_t reg_count = sizeof(jmp_buf) / sizeof(uintptr_t);
        for (size_t i = 0; i < reg_count; i++) {
            gc_heap_t *h = find_allocated_object_heap(reg_words[i]);
            if (h != NULL) {
                bitmap_mark_obj(h, reg_words[i] - Header_size);
            }
        }
        if (t->safepoint_sp != 0 && t->root_start != 0) {
            uintptr_t lo = (t->safepoint_sp < t->root_start) ? t->safepoint_sp : t->root_start;
            uintptr_t hi = (t->safepoint_sp < t->root_start) ? t->root_start : t->safepoint_sp;
            bitmap_mark_stack_range(lo, hi);
        }
    }

    /* 2. Mark registered global value slots */
    for (size_t i = 0; i < _global_roots_count; i++) {
        uintptr_t candidate = (uintptr_t)(*_global_roots[i]);
        gc_heap_t *h = find_allocated_object_heap(candidate);
        if (h != NULL) {
            bitmap_mark_obj(h, candidate - Header_size);
        }
    }

    /* 3. Trace values held inside active/reachable Tasks, Channels, MVars, and Actors to a fixed point */
    gs_conc_mark_roots();

    /* 4. Reclaim unreachable synchronization handles BEFORE `mark_bits` are cleared by `bitmap_sweep` */
    gs_conc_sweep_unreachable();

    /* 5. Sweep heap arenas and coalesce free fragments into segregated bins */
    bitmap_sweep();
    _collections++;

    if (collector != NULL) {
        collector->is_blocked_or_parked = false;
    }
    __atomic_store_n(&__gs_gc_stw_requested, 0, __ATOMIC_RELEASE);
    _stw_in_progress = false;
    pthread_cond_broadcast(&_stw_resume_cv);
}

static inline gc_heap_t *find_allocated_object_heap(uintptr_t payload_ptr)
{
    if (payload_ptr < _min_heap_addr || payload_ptr >= _max_heap_addr || (payload_ptr & (WORD_SIZE - 1)) != 0) {
        return NULL;
    }
    for (gc_heap_t *h = _heaps; h != NULL; h = h->next) {
        if (payload_ptr >= h->base + Header_size && payload_ptr < h->end) {
            uintptr_t hdr_addr = payload_ptr - Header_size;
            uintptr_t off = hdr_addr - h->base;
            if (h->alloc_bits[OFFSET_TO_IDX(off)] & OFFSET_TO_MASK(off)) {
                return h;
            }
            return NULL;
        }
    }
    return NULL;
}

static void bitmap_mark_stack_range(uintptr_t sp_low, uintptr_t sp_high)
{
    uintptr_t cur = sp_low & ~(uintptr_t)(WORD_SIZE - 1);
    for (; cur <= sp_high; cur += WORD_SIZE) {
        uintptr_t candidate = *(const uintptr_t *)cur;
        gc_heap_t *h = find_allocated_object_heap(candidate);
        if (h != NULL) {
            bitmap_mark_obj(h, candidate - Header_size);
        }
    }
}

typedef struct {
    gc_heap_t *heap;
    uintptr_t hdr_addr;
} gc_mark_entry_t;

static gc_mark_entry_t *_mark_stack = NULL;
static size_t _mark_stack_cap = 0;

static void mark_stack_push(gc_heap_t *heap, uintptr_t hdr_addr, size_t *sp)
{
    if (*sp >= _mark_stack_cap) {
        size_t next_cap = _mark_stack_cap == 0 ? 4096 : _mark_stack_cap * 2;
        gc_mark_entry_t *grown = (gc_mark_entry_t *)realloc(_mark_stack, next_cap * sizeof(gc_mark_entry_t));
        if (grown == NULL) {
            fprintf(stderr, "GC mark stack allocation failed\n");
            abort();
        }
        _mark_stack = grown;
        _mark_stack_cap = next_cap;
    }
    _mark_stack[*sp].heap = heap;
    _mark_stack[*sp].hdr_addr = hdr_addr;
    (*sp)++;
}

static bool bitmap_mark_obj(gc_heap_t *root_heap, uintptr_t root_hdr_addr)
{
    uintptr_t root_off = root_hdr_addr - root_heap->base;
    size_t root_idx = OFFSET_TO_IDX(root_off);
    bitmap_t root_mask = OFFSET_TO_MASK(root_off);

    if (root_heap->mark_bits[root_idx] & root_mask) {
        return false;
    }
    root_heap->mark_bits[root_idx] |= root_mask;

    header_t root_hdr = *(const header_t *)root_hdr_addr;
    if (Is_noscan_hdr(root_hdr)) {
        return true;
    }

    size_t sp = 0;
    mark_stack_push(root_heap, root_hdr_addr, &sp);

    while (sp > 0) {
        sp--;
        uintptr_t hdr_addr = _mark_stack[sp].hdr_addr;
        header_t hdr_val = *(const header_t *)hdr_addr;
        if (Is_noscan_hdr(hdr_val)) {
            continue;
        }
        size_t payload_words = Get_payload_words_hdr(hdr_val);
        const uintptr_t *fields = (const uintptr_t *)(hdr_addr + Header_size);

        for (size_t i = 0; i < payload_words; i++) {
            uintptr_t field_val = fields[i];
            gc_heap_t *child_heap = find_allocated_object_heap(field_val);
            if (child_heap != NULL) {
                uintptr_t child_hdr = field_val - Header_size;
                uintptr_t coff = child_hdr - child_heap->base;
                size_t cidx = OFFSET_TO_IDX(coff);
                bitmap_t cmask = OFFSET_TO_MASK(coff);
                if ((child_heap->mark_bits[cidx] & cmask) == 0) {
                    child_heap->mark_bits[cidx] |= cmask;
                    if (!Is_noscan_hdr(*(const header_t *)child_hdr)) {
                        mark_stack_push(child_heap, child_hdr, &sp);
                    }
                }
            }
        }
    }
    return true;
}

static void bitmap_sweep(void)
{
    free_list_clear();
    size_t sum_total = 0;
    size_t sum_free = 0;

    for (gc_heap_t *h = _heaps; h != NULL; h = h->next) {
        sum_total += h->total_words;
        uintptr_t cur = h->base;
        uintptr_t free_start = 0;
        size_t free_words = 0;

        while (cur < h->end) {
            uintptr_t off = cur - h->base;
            size_t word_off = WORD_INDEX(off);
            size_t idx = word_off / BITS_PER_BITMAP;
            size_t bit = word_off % BITS_PER_BITMAP;
            bitmap_t alloc_word = h->alloc_bits[idx];

            /* Fast-skip 64 unallocated words at once when aligned to a bitmap word */
            if (bit == 0 && alloc_word == 0) {
                if (free_words == 0) {
                    free_start = cur;
                }
                free_words += BITS_PER_BITMAP;
                cur += BITS_PER_BITMAP * WORD_SIZE;
                continue;
            }

            bitmap_t mask = ((bitmap_t)1) << bit;
            if (alloc_word & mask) {
                header_t hdr_val = *(const header_t *)cur;
                size_t obj_total_words = Get_payload_words_hdr(hdr_val) + 1;

                if (h->mark_bits[idx] & mask) {
                    if (free_words >= 2) {
                        sum_free += free_words;
                        free_list_insert(free_start, free_words);
                    }
                    free_words = 0;
                } else {
                    h->alloc_bits[idx] &= ~mask;
                    if (free_words == 0) {
                        free_start = cur;
                    }
                    free_words += obj_total_words;
                }
                cur += obj_total_words * WORD_SIZE;
            } else {
                /* Skip remaining trailing zero bits in this bitmap word up to the next set bit */
                bitmap_t remaining = alloc_word >> bit;
                size_t skip = (remaining == 0) ? (BITS_PER_BITMAP - bit) : (size_t)__builtin_ctzll(remaining);
                if (free_words == 0) {
                    free_start = cur;
                }
                free_words += skip;
                cur += skip * WORD_SIZE;
            }
        }

        if (free_words >= 2) {
            sum_free += free_words;
            free_list_insert(free_start, free_words);
        }

        memset(h->mark_bits, 0, h->bitslen * sizeof(bitmap_t));
    }
    _last_sweep_total_words = sum_total;
    _last_sweep_free_words = sum_free;
}
