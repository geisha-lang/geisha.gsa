#ifndef GC_H
#define GC_H

#include <stdbool.h>
#include <stdint.h>
#include <stddef.h>
#include <stdlib.h>
#include <string.h>

#include "gsvalue.h"

/* Relaxed/seq_cst atomic flag polled by LLVM-generated loop backedges & function prologues */
extern int32_t __gs_gc_stw_requested;

void gc_init(size_t init_size_words);
void gc_init_with_stack(size_t init_size_words, void *stack_anchor);
void gc_enable_generational(void);
void gc_register_root(void **slot);
void gc_run_globals_init_once(int32_t *state, void (*init_fn)(void));

/* Multicore thread lifecycle & cooperative safepoint / lock-free blocking-section protocol */
void gc_thread_attach(void *stack_anchor);
void gc_thread_detach(void);
void gc_safepoint_slow(void);
void gc_enter_blocking(void *jmp_buf_on_stack);
void gc_leave_blocking(void);

/* Allocation APIs */
void *gc_alloc(size_t size_bytes);
void *gc_alloc_atomic(size_t size_bytes);
void *gc_alloc_atomic_uninit(size_t size_bytes);
void *gc_alloc_masked(size_t size_bytes, uint64_t ptr_mask);

/* Sticky generational write barrier (called on pointer mutations to Cell / MutArray) */
void gc_write_barrier(void *container_ptr);

/* Diagnostics & explicit collection */
void gc_collect_major(void);
void gc_trim(void);
void gc_set_thresholds(size_t minor_bytes, size_t major_bytes);
void gc_set_mem_limit(size_t soft_limit_bytes);
size_t gc_collection_count(void);
size_t gc_minor_collection_count(void);
size_t gc_major_collection_count(void);
size_t gc_heap_live_bytes(void);

/* Embedded C/Swift host lifecycle & StableHandle table (GC-rooted opaque handles) */
void geisha_rt_init(void);
int64_t gc_host_enter(void *stack_anchor);
void gc_host_leave(int64_t token);
int64_t gc_handle_new(void *obj);
void *gc_handle_get(int64_t handle);
void gc_handle_free(int64_t handle);

/* STW hooks used by `gs_conc.c` to trace in-flight concurrent containers & finalize dead handles */
bool gc_is_obj_marked(const void *payload_ptr);
bool gc_mark_ptr(const void *payload_ptr);

/* Two-phase GC Cleanup (non-resurrecting finalizer) + External Memory Pressure accounting */
typedef void (*gc_cleanup_fn)(void *arg);
int64_t gc_cleanup_register(void *owner, gc_cleanup_fn fn, void *arg, size_t external_bytes);
bool gc_cleanup_cancel(int64_t token);
size_t gc_external_live_bytes(void);

/* GC-managed ForeignPtr (binds external raw pointer + cleanup + external bytes to a GC object) */
void *gc_foreign_ptr_new(void *raw_ptr, gc_cleanup_fn fn, size_t external_bytes);
void *gc_foreign_ptr_alloc(int64_t size_bytes);
void *gc_foreign_ptr_get(void *fp);

/* Scoped bump-pointer Arena for NoScan raw byte buffers (destroyed deterministically on scope exit) */
void *gc_arena_new(void);
void *gc_arena_alloc(void *arena, int64_t size_bytes);
void gc_arena_destroy(void *arena);

#ifdef __DEBUG
#ifndef __DEBUG_OUT
#define __DEBUG_OUT stderr
#endif
#endif

#endif
