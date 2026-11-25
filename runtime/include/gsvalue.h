#ifndef GSVALUE_H
#define GSVALUE_H

#include <stdint.h>
#include <stddef.h>
#include <stdbool.h>

typedef uintptr_t header_t;
typedef header_t value_t;

#define WORD_SIZE (sizeof(void *))

/*
 * 64-bit Object Header Layout (stored immediately before every 8-byte-aligned payload):
 *   Bit  0:      HEADER_NOSCAN_BIT      (1 = leaf object containing no GC pointers)
 *   Bit  1:      HEADER_REMEMBERED_BIT  (1 = old-gen object already recorded in thread remset)
 *   Bit  2:      HEADER_HAS_MASK_BIT    (1 = bits [24..63] hold an exact 40-bit word pointer mask)
 *   Bits 3..23:  payload_words          (21 bits, up to 2,097,151 words; large objs use gc_large_t)
 *   Bits 24..63: ptr_mask               (40-bit exact pointer bitmask when HEADER_HAS_MASK_BIT == 1)
 */
#define HEADER_NOSCAN_BIT      ((header_t)1ULL)
#define HEADER_REMEMBERED_BIT  ((header_t)2ULL)
#define HEADER_HAS_MASK_BIT    ((header_t)4ULL)
#define HEADER_WORDS_SHIFT     3u
#define HEADER_WORDS_MASK      ((header_t)0x1FFFFFULL)
#define HEADER_MASK_SHIFT      24u

/* Pointer `p` points to object payload right after the 1-word header */
#define Get_head(p) (*((header_t *)(p) - 1))
#define Header_size (sizeof(header_t))

#define Is_noscan_hdr(h)     (((h) & HEADER_NOSCAN_BIT) != 0)
#define Is_remembered_hdr(h) (((h) & HEADER_REMEMBERED_BIT) != 0)
#define Has_ptr_mask_hdr(h)  (((h) & HEADER_HAS_MASK_BIT) != 0)
#define Get_payload_words_hdr(h) ((size_t)(((h) >> HEADER_WORDS_SHIFT) & HEADER_WORDS_MASK))
#define Get_ptr_mask_hdr(h)      ((uint64_t)((h) >> HEADER_MASK_SHIFT))

static inline header_t make_gc_header(size_t payload_words, bool noscan, bool has_mask, uint64_t ptr_mask)
{
    header_t w = ((header_t)(payload_words & HEADER_WORDS_MASK)) << HEADER_WORDS_SHIFT;
    header_t flags = (noscan ? HEADER_NOSCAN_BIT : (header_t)0)
                   | (has_mask ? HEADER_HAS_MASK_BIT : (header_t)0);
    header_t m = has_mask ? (((header_t)ptr_mask) << HEADER_MASK_SHIFT) : (header_t)0;
    return w | flags | m;
}

#endif
