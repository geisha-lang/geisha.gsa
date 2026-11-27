# Core Geisha Formal Semantics & Machine-Checked Metatheory

This directory contains the complete machine-checked formal semantics and safety proofs of **Core Geisha** in **Lean 4** (`v4.36.0`), corresponding to the post-monomorphization Core IR (`src/core.gsa`), codegen layout (`src/codegen.gsa`), generational bitmap GC (`runtime/runtime/gc_bitmap.c`), and concurrency runtime (`runtime/runtime/gs_conc.c`) of the self-hosted compiler `geisha.gsa`.

## 1. Module Overview

| File | Contents |
| --- | --- |
| `CoreGeisha/Syntax.lean` | Monomorphic types `Ty` (including `Int64`, `Float`, `Float32`, `Char`, `Ptr`, `ScopedPtr`, `Arena`, `ForeignPtr`, `AtomicInt`, `Cell`, `MutArray`, `ImmArray`, `Task`, `MVar`, `Chan`, `Actor`), closure capture modes `Mode` (`local` / `shared`), synchronization/actor primitives `ConcPrim`, host/C declarations `ExternDecl`, literals `Lit`, operators `UnOp`/`BinOp`, patterns `Pat`, expressions `Expr`, runtime traps `Trap` (`divByZero` / `matchFailure` / `hostTrap`), values `IsValue`, heap `Store`, `freeVars`, `exprLocs`, and substitution `subst`/`substMany`. |
| `CoreGeisha/Typing.lean` | Declarative static semantics (`HasType`, `ConcPrimHasType`), capture-mode subtyping (`ModeSub`, `TySub` with `shared <: local` and invariant `Cell`/`MVar`/`Chan`/`Actor`), coinductive `IsSend` (Park greatest fixed point supporting recursive ADTs, `MVar`/`Chan`, and unconditionally `Send` `Actor s` encapsulating `!Send` state `s`), and lexical `shared` closure capture checking. |
| `CoreGeisha/Semantics.lean` | Strict left-to-right small-step operational semantics (`Step`, `StepConcPrim`), interleaved concurrent pool semantics (`ConcPool`, `ConcStep`, `ConcSteps`) modeling `Task`s, synchronized `MVar`s, bounded/unbounded MPMC `Chan`s, and sequential thread-pinned `Actor`s (`init` / `idle` / `busy` / `failed` + FIFO mailbox), legitimate synchronization blocking (`BlockedOnTask`), and active cell race detection (`ActiveCellAccess`, `HasDataRace`). |
| `CoreGeisha/Soundness.lean` | Zero-`sorry` proofs of **Subtyping Transitivity & Admissibility**, **Coinductive `IsSend` Unfolding**, **Zero-Location Lemma** (`exprLocs_empty_of_isValue_isSend`), **Weakening**, **Substitution**, **Canonical Forms**, **Progress**, **Preservation**, and **Sequential Type Safety**. |
| `CoreGeisha/Concurrency.lean` | Zero-`sorry` proofs of **Global Heap Ownership Partition** (`HeapOwned` across `ThreadId.task` and `ThreadId.actor`), **Concurrent Type Safety** (`conc_type_safety`), **Pairwise Heap Disjointness** (`conc_heap_disjoint` across Task-Task, Task-Actor, and Actor-Actor), and **Compile-Time Data-Race Freedom** (`conc_data_race_freedom`). |
| `CoreGeisha/Exhaustive.lean` | Executable **Maranget Pattern-Matrix Exhaustiveness Checker** (`checkPatsExhaustive`, `checkProgramExhaustive`) and zero-`sorry` proofs of matrix specialization soundness (`checkArmsExhaustive_sound`), dynamic match-coverage preservation (`step_preserves_exhSafe`), and **Complete Elimination of `Trap.matchFailure`** (`exhaustive_no_match_failure`, `conc_exhaustive_no_match_failure`). |
| `CoreGeisha/Escape.lean` | Executable **Escape Analysis Verifier** (`checkProgramEscape`), explicit **Stack-Frame Region Operational Semantics** (`RExpr`, `RStore`, `popRegion`, `IsDanglingAccess`), non-vacuity counterexample (`dangling_access_nonvacuous`), **Zero Use-After-Return / No Dangling Stack Pointers** (`escape_no_dangling_pointers`), and **Stack-vs-Heap Observational Simulation** (`stack_alloc_simulates_heap`). |
| `CoreGeisha/Scoped.lean` | Zero-`sorry` proofs of the **3-Point Capture-Mode Lattice** (`shared <: local <: scoped`, `modeJoin_lub`), **Thread-Safe Non-Escape** (`isSend_implies_noScoped`), **Scoped Region Memory Safety** (`noScoped_value_has_no_regions`, `scoped_preservation`, `scoped_no_dangling_access` / `¬DanglingScopedAccess`, `dangling_scoped_nonvacuous`), and **`ImmArray` / `parTabulate` Disjoint-Chunk Data-Race Freedom** (`parTabulate_chunks_disjoint`, `parTabulate_chunks_cover`, `parTabulate_data_race_free`). |
| `CoreGeisha/GC.lean` | Formalization of **40-Bit Exact Object Pointer Masks** (`computePtrMask_sound`, `adtVariantPtrMask_sound` with scalar false-pointer immunity, plus `checkEmittedGcMasks` LP64 byte-offset & unboxed-ADT cross-checking against `src/codegen.gsa`) and **Sticky-Mark Generational GC & Write Barrier** (`GenHeapInv`, `gcAllocImmutable_preserves_inv`, `gcWriteBarrierStore_preserves_inv`, UAF counterexample `missing_write_barrier_unsound`, `minorGc_sound`, `majorGc_sound`, and `majorGc_complete`). |
| `CoreGeisha/Eval.lean` | Fuel-bounded deterministic small-step evaluator (`stepOnce`, `runSteps`) with zero-`sorry` soundness proof (`runSteps_sound`) for `geisha-check --eval` differential conformance testing against native LLVM binaries. |
| `CoreGeisha/Checker.lean` | Unified verified executable checker (`checkProgram`) combining type/mode/concurrency checking, Maranget exhaustiveness, stack-escape checking, and live codegen GC mask verification, linked directly to end-to-end safety theorems. |
| `CoreGeisha/Parser.lean` | `.gscore` S-expression parser for `--dump-core` translation validation (`adts`, `externs`, `funs`, `stack-allocs`, `gc-masks`), supporting full self-verification of `src/geisha.gsa`. |

## 2. Key Machine-Checked Guarantees

1. **Sequential & Concurrent Type Safety (`¬ IsStuck`)**:
   Every active `Task` and `Actor` thread either terminates (as a value or defined `divByZero` trap), legitimately blocks on an unfulfilled `Task`/`MVar`/`Chan` synchronization primitive (`BlockedOnTask`), or takes a deterministic step.
2. **Elimination of `Trap.matchFailure` (`Exhaustive.lean`)**:
   Programs passing `checkProgramExhaustive` never evaluate to `Trap.matchFailure` (nor put any `Actor` into `.failed .matchFailure`) across arbitrary sequential or concurrent interleavings.
3. **Compile-Time Data-Race Freedom with `!Send`-State Actors (`Concurrency.lean`)**:
   `Actor s` is unconditionally `IsSend` even when `s` is `!Send` (`Cell τ` or `local` closures), because `actorSpawn` requires a `shared` `() => s` initializer (`exprLocs = []`), `actorCall`/`actorSend` require `shared` `s => r` handlers (`IsSend r`), and each actor processes its mailbox sequentially on a dedicated `ThreadId.actor aid`, preserving `¬ HasDataRace pool`.
4. **Stack-Frame Region Safety & Heap Refinement (`Escape.lean`)**:
   Stack-promoted `Cell` allocations freed eagerly upon function return (`popRegion`) never produce dangling stack dereferences (`¬ IsDanglingAccess`) and are simulated lockstep by heap semantics (`stack_alloc_simulates_heap`).
5. **Exact 40-Bit Pointer Masks & Sticky Generational Write Barrier (`GC.lean`)**:
   Immutable young allocations require zero write barriers; mutating heap containers with `gcWriteBarrierStore` preserves `GenHeapInv`; `minorGcCollect` preserves all reachable objects (`minorGc_sound`, whereas omitting the write barrier sweeps a live object in `missing_write_barrier_unsound`); `majorGcCollect` reclaims unreachable cyclic old-generation islands (`majorGc_complete`).

## 3. Verification

```sh
cd formal && lake build
make verify-core
```

All 11 modules compile cleanly under Lean 4 (`v4.36.0`) with **zero `sorry`**, **zero custom axioms**, and **zero external library dependencies**.
