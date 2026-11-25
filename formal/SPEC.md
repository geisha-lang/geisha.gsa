# Core Geisha Formal Semantics Specification

This directory contains the machine-checked formal semantics of **Core Geisha** in **Lean 4**, corresponding to the post-monomorphization Core IR (`src/core.gsa`) of the self-hosted compiler `geisha.gsa`.

## 1. Module Overview

| File | Contents |
| --- | --- |
| `CoreGeisha/Syntax.lean` | Monomorphic types `Ty`, closure capture modes `Mode` (`local` / `shared`), `Task` handles, literals `Lit`, operators `UnOp`/`BinOp`, patterns `Pat`, expressions `Expr` (including `spawn`/`await`), runtime traps `Trap`, values `IsValue`, heap `Store`, `freeVars`, `exprLocs`, and closed-value substitution `subst`/`substMany`. |
| `CoreGeisha/Typing.lean` | Independent declarative static semantics (`HasType`, `HasTypes`, `PatHasType`, `ArmsHaveType`), capture-mode subtyping (`ModeSub`, `TySub` with `shared <: local` and invariant `Cell`), coinductive `IsSend` (Park greatest fixed point supporting recursive ADTs), and lexical `shared` closure capture checking. |
| `CoreGeisha/Semantics.lean` | Strict left-to-right small-step operational semantics (`Step`, `StepList`), interleaved concurrent task-pool semantics (`ConcStep`, `ConcSteps`), legitimate task-join waiting (`BlockedOnTask`), and active cell memory-access characterization (`ActiveCellAccess`, `HasDataRace`). |
| `CoreGeisha/Soundness.lean` | Zero-`sorry` machine-checked proofs of **Subtyping Transitivity**, **Coinductive `IsSend` Unfolding**, **Zero-Location Lemma** (`exprLocs_empty_of_isValue_isSend`), **Weakening**, **Substitution**, **Canonical Forms**, **Progress**, and **Preservation**. |
| `CoreGeisha/Concurrency.lean` | Zero-`sorry` machine-checked proofs of **Global Heap Ownership Partition** (`HeapOwned`), **Concurrent Type Safety** (`conc_type_safety`), **Cross-Thread Heap Disjointness** (`conc_heap_disjoint`), and **Compile-Time Data-Race Freedom** (`conc_data_race_freedom`). |
| `CoreGeisha/Checker.lean` | Verified executable type & concurrency checker (`checkProgram`, greatest-fixed-point `computeSendAdts`/`checkSendAdtsClosed`) linked end-to-end to `verified_concurrent_program_safety` and `verified_program_data_race_freedom`. |
| `CoreGeisha/Parser.lean` | `.gscore` S-expression parser for `--dump-core` translation validation. |

## 2. Explicit Semantic Decisions

1. **Evaluation Order**:
   - Strict call-by-value, **left-to-right** for tuples, multi-arg closure/direct calls (`callee` first, then `arg_1, …, arg_n`), ADT constructor fields, `cellSet(e1, e2)`, and non-short-circuiting binary operators.
   - `&&` and `||` are **short-circuiting** on the left operand.
   - `while c b` unfolds to `if c { b; while c b } else ()`.

2. **Arithmetic & Traps vs. Undefined Behavior**:
   - `Int` (`Int32`) arithmetic (`+`, `-`, `*`, unary `-`, bitwise) uses **two's-complement wrapping** semantics (never UB).
   - Division (`/`) and remainder (`%`) by `0` produce `Trap.divByZero`; falling off `match` arms produces `Trap.matchFailure`.
   - Traps propagate strictly through all evaluation contexts and across `await` boundaries (`awaitTaskTrap`).

3. **Capture-Mode `Send` Discipline & Compile-Time Data-Race Freedom**:
   - Mutable state is isolated to `Cell τ` (`¬ IsSend`), while ADTs, tuples, primitives, and `Task τ` (for `IsSend τ`) are immutable/thread-safe values.
   - Closures carry capture modes: `Mode.local` (may capture `Cell` or `local` closures; `¬ IsSend`) vs. `Mode.shared` (every free lexical variable must satisfy `IsSend`; `IsSend` holds).
   - Capture-mode subtyping (`Mode.shared <: Mode.local`) allows `shared` closures to be passed wherever `local` closures are expected without monomorphization duplication, while `Cell τ` remains invariant.
   - `conc_heap_disjoint` and `conc_data_race_freedom` prove that across all nondeterministic thread interleavings (`ConcSteps`), distinct tasks hold pairwise disjoint sets of `Cell` heap locations (`¬ HasDataRace tasks`).

## 3. Alignment with `geisha.gsa` and Next Extensions

| Layer | Current Status | Next Step |
| --- | --- | --- |
| Monomorphic Core IR (`src/core.gsa`) | **Formalized & Type-Soundness Proved (Lean 4)** | Add `MutArray` (bounds-checked trap) & `Float`/`Int64` |
| Concurrency, Capture Modes & `Send` (`Task`, `Cell`) | **Formalized & Data-Race Freedom Proved (Lean 4)** | Extend with blocking channels (`MVar`/`Chan`) & `Actor` |
| Surface HM + Open Concepts (`src/infer.gsa`) | Algorithm in `infer.gsa` | Formalize declarative HM + `SendIf` constraint solving |
| Pattern Exhaustiveness (Maranget in `src/infer.gsa`) | Algorithm in `infer.gsa` | Prove exhaustive `match` never produces `Trap.matchFailure` |
| Escape Analysis (`src/core.gsa`) | 2-phase fixed-point in `core.gsa` | Add region/stack store semantics and prove stack-allocation refinement |

## 4. Verification

```sh
cd formal
lake build
```

All theorems compile cleanly under Lean 4 (`v4.36.0`) with **zero `sorry`** and no external library dependencies.
