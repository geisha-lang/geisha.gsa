#ifndef GC_BITMAP_H
#define GC_BITMAP_H

#include <stdint.h>
#include <stddef.h>
#include <stdbool.h>

#include "gc.h"

/*
 * Size-Class Slab + Lazy-Sweep + Sticky-Generational GC Layout
 *
 * - Page size: 16 KB (matches macOS arm64 hardware page size for exact madvise reclamation)
 * - Chunk size: 4 MB (256 pages, 4 MB aligned via mmap)
 * - Pages 0..4 of each chunk store chunk metadata + 256 `gc_page_t` descriptors (<2% overhead)
 * - Pages 5..255 (251 usable pages) hold 16 KB size-class slabs
 * - Objects > 4096 bytes (including 8B header) are directly mmap'd and munmap'd on sweep
 */
#define GC_PAGE_SHIFT       14u
#define GC_PAGE_SIZE        ((size_t)1u << GC_PAGE_SHIFT)    /* 16 KB */
#define GC_CHUNK_SHIFT      22u
#define GC_CHUNK_SIZE       ((size_t)1u << GC_CHUNK_SHIFT)   /* 4 MB */
#define GC_PAGES_PER_CHUNK  (GC_CHUNK_SIZE >> GC_PAGE_SHIFT) /* 256 */
#define GC_NUM_CLASSES      31u
#define GC_MAX_SMALL_BYTES  4096u
#define GC_BITMAP_WORDS     16u /* 16 * 64 = 1024 max slots per 16 KB page (min slot 16 B) */

typedef struct gc_free_slot_t {
    struct gc_free_slot_t *next;
    uint16_t slot_idx;
} gc_free_slot_t;

typedef enum {
    GC_PAGE_FREE = 0,
    GC_PAGE_INUSE = 1,
} gc_page_state_t;

typedef struct gc_page_t {
    struct gc_page_t *next;
    struct gc_page_t *prev;
    gc_free_slot_t *free_list;
    uintptr_t base;
    uint32_t sweep_gen;
    uint16_t slot_size;
    uint16_t num_slots;
    uint16_t bump_idx;
    uint16_t live_count;
    uint8_t state;
    uint8_t size_class;
    uint8_t list_kind; /* 0 = none/local, 1 = unswept, 2 = full, 3 = free */
    uint8_t _pad;
    uint64_t alloc_bits[GC_BITMAP_WORDS];
    uint64_t mark_bits[GC_BITMAP_WORDS];
} gc_page_t;

typedef struct gc_chunk_t {
    struct gc_chunk_t *next;
    uintptr_t base;
    size_t first_data_page;
    gc_page_t pages[GC_PAGES_PER_CHUNK];
} gc_chunk_t;

typedef struct gc_large_t {
    struct gc_large_t *next;
    struct gc_large_t *prev;
    size_t map_size;
    size_t payload_words;
    uintptr_t payload_ptr;
    bool marked;
} gc_large_t;

#endif
