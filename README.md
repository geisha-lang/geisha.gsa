# geisha.gsa

Self-hosting compiler for the **Geisha** programming language, written in Geisha and targeting **LLVM 20 opaque-pointer IR**.

## Architecture

`geisha.gsa` implements the complete Geisha language pipeline in ~6,800 lines of pure Geisha (`src/`) linked with a small portable C11 runtime (`runtime/`):

| Module | Responsibility |
| --- | --- |
| `src/ast.gsa` | Core AST, Hindley-Milner `Type`/`Scheme`, patterns, module items, and 15-level Scala/Swift-style operator precedence table |
| `src/lexer.gsa` | Linear-time tokenizer with newline tracking (`hadNewline`), nested block comments, escapes, and custom symbolic operators |
| `src/parser.gsa` | Recursive-descent + Pratt expression parser, `(op)` operator sections, destructuring `let`, and `Result` early-return `?` desugaring |
| `src/stdlib_bundle.gsa` | Embedded `std.*` and `sys.*` standard library sources (generated from `stdlib/` via `scripts/gen_stdlib.py`) |
| `src/loader.gsa` | Multi-file & inline `mod` loader, cycle-checked topological sort, `pub use` re-exports, and longest-prefix module vs `.field` disambiguation |
| `src/infer.gsa` | Hindley-Milner type inference, open Concepts & Instances (including arithmetic/comparison/bitwise operator overloading), `Send` checking, `.field` resolution, mutual recursion backfill, and Maranget exhaustiveness checking |
| `src/core.gsa` | K-conversion, polymorphic local lambda lifting, deterministic closure conversion, demand-driven worklist monomorphization, static Concept dispatch, concurrent closure `Send` verification, and 2-phase interprocedural escape analysis |
| `src/codegen.gsa` | Static LP64 ABI layout calculator and LLVM 20 opaque-pointer textual IR (`.ll`) emitter |
| `src/mod.gsa` | Command-line compiler driver (`-e`, `-c`, `-o`, `--src-root`, `--runtime`) |

## Bootstrapping & Fixed-Point Verification

Prerequisites:
- Stage 0 bootstrap compiler [`miko`](https://github.com/geisha-lang/miko) on `$PATH` (or `STAGE0=/path/to/miko`)
- Clang / LLVM toolchain (`cc` supporting `-x ir`) and `ar`

Run the full 3-stage bootstrap and verify the fixed point (`stage2.ll == stage3.ll`):

```sh
make bootstrap STAGE0=/path/to/miko
```

Run the end-to-end language test suite compiled by the self-hosted Stage 2 compiler (`build/geisha2`):

```sh
make test
```

## CLI Usage

```sh
# Compile a single-file program to a native executable
./build/geisha2 -o hello hello.gsa

# Compile a multi-file project
./build/geisha2 --src-root . -o my_app src/mod.gsa

# Emit LLVM 20 IR (.ll)
./build/geisha2 -e -o hello.ll hello.gsa
```
