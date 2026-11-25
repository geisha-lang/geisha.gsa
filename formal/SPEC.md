# Core Geisha Formal Semantics Specification

This directory contains the machine-checked formal semantics of **Core Geisha** in **Lean 4**, corresponding to the post-monomorphization Core IR (`src/core.gs`) of the self-hosted compiler `geisha.gs`.

## 1. Module Overview

| File | Contents |
| --- | --- |
| `CoreGeisha/Syntax.lean` | Monomorphic types `Ty`, literals `Lit`, operators `UnOp`/`BinOp`, patterns `Pat`, expressions `Expr`, runtime traps `Trap`, values `IsValue`, heap `Store`, and closed-value substitution `subst`/`substMany`. |
| `CoreGeisha/Typing.lean` | Independent declarative static semantics (`HasType`, `HasTypes`, `PatHasType`, `ArmsHaveType`, `FunEnvTyped`, `StoreTyped`, `StoreExtends`). |
| `CoreGeisha/Semantics.lean` | Strict left-to-right small-step operational semantics (`Step`, `StepList`, `Steps`), total pattern matcher (`matchPat`), and explicit trap propagation (`IsTerminal`, `IsStuck`). |
| `CoreGeisha/Soundness.lean` | Zero-`sorry` machine-checked proofs of **Weakening**, **Substitution**, **Pattern-Match Typing**, **Canonical Forms**, **Progress**, **Preservation**, and **Multi-Step Type Safety**. |

## 2. Explicit Semantic Decisions (Closing Previous Gaps)

To separate **specification** from **implementation** (`geisha.gs` + LLVM 20 + `runtime/*.c`), Core Geisha pins down the following rules:

1. **Evaluation Order**:
   - Strict call-by-value, **left-to-right** for tuples, multi-arg closure/direct calls (`callee` first, then `arg_1, …, arg_n`), ADT constructor fields, `cellSet(e1, e2)`, and non-short-circuiting binary operators.
   - `&&` and `||` are **short-circuiting** on the left operand.
   - `while c b` unfolds to `if c { b; while c b } else ()`.

2. **Arithmetic & Traps vs. Undefined Behavior**:
   - `Int` (`Int32`) arithmetic (`+`, `-`, `*`, unary `-`, bitwise) uses **two's-complement wrapping** semantics (never UB).
   - Division (`/`) and remainder (`%`) by `0` produce a **defined runtime trap** (`Trap.divByZero`), not UB.
   - Falling off the end of `match` arms produces a **defined runtime trap** (`Trap.matchFailure`).
   - Traps propagate strictly out of every evaluation context (`let`, `if`, `match`, `apply`, `tuple`, `makeData`, `cell*`, etc.).
   - **Type Safety (`type_safety`)** proves that a well-typed closed program **never gets stuck** (`¬ IsStuck`): every step either yields a `Value`, raises a defined `Trap`, or makes progress.

3. **Immutable Values vs. Mutable Store (`Cell`)**:
   - ADTs (`makeData`), tuples, and closures are **immutable values** in the core semantics.
   - Mutability is isolated to `Cell τ` (`cellNew`, `cellGet`, `cellSet`), modeled via a typed monotone heap `σ : Store` / `Ψ : StoreTy`.
   - This establishes the semantic foundation for proving that `src/core.gs`'s **escape analysis** (stack-allocating non-escaping ADTs) is an observationally equivalent refinement.

4. **Multi-Argument Uncurried Functions & Direct Calls**:
   - Mirrors `geisha.gs`'s `TmMakeCls` / `TmApplyCls` / `TmApplyDir`: functions take fixed-arity parameter lists `List (Ident × Ty)` without implicit currying.

## 3. Alignment with `geisha.gs` and Next Extensions

| Layer | Current Status | Next Step |
| --- | --- | --- |
| Monomorphic Core IR (`src/core.gs` 16 `Term`s) | **Formalized & Type-Soundness Proved (Lean 4)** | Add `MutArray` (bounds-checked trap) & `Float`/`Int64` |
| Surface HM + Open Concepts (`src/infer.gs`) | Algorithm in `infer.gs` | Formalize declarative HM + Value Restriction + Concept coherence, and prove elaboration/monomorphization preserves typing |
| Pattern Exhaustiveness (Maranget in `src/infer.gs`) | Algorithm in `infer.gs` | Prove exhaustive `match` never produces `Trap.matchFailure` |
| Escape Analysis (`src/core.gs`) | 2-phase fixed-point in `core.gs` | Add region/stack store semantics and prove stack-allocation refinement |
| Concurrency & `Send` (`runtime/gs_conc.c`) | C11 `pthread` + `SEQ_CST` | Formalize interleaved threads + `Send` data-race freedom |

## 4. Verification

```sh
cd formal
lake build
```

All theorems compile cleanly under Lean 4 (`v4.36.0`) with **zero `sorry`** and no external library dependencies.
