# The Geisha Language Specification

**Version:** `0.2` (matches `geisha.gsa` `v0.2.0`)
**Status:** Living normative reference for the Geisha programming language, type system, memory & concurrency model, package manager, and compiler targets.
**Formal Core:** See [`formal/SPEC.md`](../formal/SPEC.md) for the machine-checked Lean 4 formalization of Core Geisha.

---

## Table of Contents

1. [Overview & Design Philosophy](#1-overview--design-philosophy)
2. [Lexical Structure](#2-lexical-structure)
3. [Expressions, Statements & Operator Precedence](#3-expressions-statements--operator-precedence)
4. [Script Mode & Program Entry](#4-script-mode--program-entry)
5. [Type System & Hindley-Milner Inference](#5-type-system--hindley-milner-inference)
6. [Concepts, Instances & Generic Deriving](#6-concepts-instances--generic-deriving)
7. [Pattern Matching & Exhaustiveness](#7-pattern-matching--exhaustiveness)
8. [Modules, Visibility & Resolution](#8-modules-visibility--resolution)
9. [Memory Model, Escape Analysis & Scoped Regions](#9-memory-model-escape-analysis--scoped-regions)
10. [Concurrency & `Send` Safety](#10-concurrency--send-safety)
11. [C FFI & Compilation Targets](#11-c-ffi--compilation-targets)
12. [Package Management (`geisha.toml` & MVS)](#12-package-management-geishatoml--mvs)
13. [Compiler Diagnostics & Agent Tooling](#13-compiler-diagnostics--agent-tooling)

---

## 1. Overview & Design Philosophy

**Geisha** (`.gsa`) is a statically typed, functional-imperative programming language compiled ahead-of-time via **LLVM 20 opaque-pointer IR** to native binaries/libraries (`native`, `ios`, `ios-sim`) and WebAssembly (`wasm32`).

Geisha is built around five core invariants:

1. **ML Expressiveness with Practical Mutability**: Full Hindley-Milner type inference, algebraic data types (ADTs), exhaustive pattern matching, and open Concepts/Instances, paired with explicit `Cell a` / `MutArray a` mutability and C-style `while` loops.
2. **Compile-Time Data-Race Freedom**: A coinductive `Send` concept and 3-point closure capture-mode lattice (`shared <: local <: scoped`) prevent unsynchronized shared mutable state across threads, while allowing `Actor s` to encapsulate `!Send` local state safely.
3. **Zero-Copy Scoped Regions**: `ForeignPtr`, `ScopedPtr`, and `Arena` provide deterministic, zero-copy FFI/memory access whose lifetimes are enforced statically via `$Scoped` capture modes and `NoScoped` escape checks.
4. **Low-Overhead Generational Runtime + Escape Analysis**: A 2-phase interprocedural escape analyzer promotes non-escaping `Cell`s to the stack; escaping heap objects use a generational bitmap GC (256 KB thread-local nursery + 31 size classes) with exact 40-bit pointer masks.
5. **Zero-Server Decentralized Packages**: Dependencies are addressed directly by Git URL (or `$GEISHA_INDEX` short names), resolved deterministically with Minimal Version Selection (MVS), and pinned by SHA-256 in `geisha.lock`.

---

## 2. Lexical Structure

### 2.1 Encoding & Shebang
- Source files are UTF-8 encoded with extension `.gsa`.
- If line 1 begins with `#!`, the lexer skips the remainder of line 1 while preserving line numbers (enabling `#!/usr/bin/env -S geisha run`).

### 2.2 Whitespace & Comments
- Spaces (`0x20`), tabs (`0x09`), carriage returns (`0x0D`), and newlines (`0x0A`) separate tokens. The lexer records `hadNewline` on each token for top-level script statement separation.
- Line comments: `// ...` until newline.
- Block comments: `/* ... */` (unterminated block comments are a lex error; `//` and `/*` terminate symbolic operator scanning).

### 2.3 Keywords
Reserved keywords:
```text
def      extern   if       else     while    let      in
type     data     match    concept  instance forall   pub
use      mod      open     as       true     false    Void
```

### 2.4 Literals & Escapes
- **Integers**: Decimal (`[0-9][0-9_]*`), hexadecimal (`0[xX][0-9a-fA-F_]+`), octal (`0[oO][0-7_]+`), and binary (`0[bB][01_]+`), typed as `Int` (32-bit signed integer; non-negative radix literals accept full 32-bit bit patterns `0x00000000`–`0xFFFFFFFF`).
- **Floats**: Decimal with fractional part and optional exponent (`[0-9][0-9_]*\.[0-9][0-9_]*([eE][+-]?[0-9][0-9_]*)?`), typed as `Float` (`f64`).
- **Booleans**: `true`, `false` (`Bool`).
- **Unit**: `()` (`Void`).
- **Characters**: Single ASCII byte `'a'` or escaped `'\n'` (`Char`).
- **Strings**: Double-quoted `"..."` (`String`, UTF-8 byte sequence).
- **Escape sequences** (in char and string literals): `\n`, `\r`, `\t`, `\0`, `\\`, `\"`, `\'`.

### 2.5 Symbolic Operators
Operator characters: `! # $ % & * + - / : < = > ? @ \ ^ | ~`.
- Standalone `?` (not followed by `?`, `>`, `=`, `:`) is lexed as `TkQuestion` (Result early-return operator).
- Reserved non-definable tokens: `=`, `:`, `->`, `=>`, `&&`, `||`, `!`, `?`.
- All other operator sequences can be defined as custom functions using parenthesized names: `def (|>)(x, f) = f(x)`.

---

## 3. Expressions, Statements & Operator Precedence

### 3.1 Blocks & Statements
A block `{ s1; s2; expr }` evaluates statements separated by `;` and yields the value of its final expression.
- Semicolons are **separators**, not terminators: `{ a; b }` is valid; `{ a; b; }` is a syntax error because a final expression is required (use `()` if `Void` is intended).
- `let` bindings inside blocks:
  - Simple: `let x = expr` or `let x: Type = expr`
  - Destructuring: `let (a, b) = pair`, `let Point { x, y } = p`

### 3.2 Control Flow
- **Conditional**: `if (cond) thenExpr else elseExpr`
  - Parentheses around `cond` are **required**.
  - The `else` branch is **always required** (use `else ()` for `Void` side effects).
- **Loop**: `while (cond) bodyExpr`
  - Parentheses around `cond` are **required**. Evaluates to `Void`.
- **Pattern Match**:
  ```geisha
  match scrutinee {
      Some(x) if (x > 0) -> x,
      Some(_) -> 0,
      None -> -1,
  }
  ```
  - Arms use `->` (not `=>`) and are comma-separated (trailing comma allowed).

### 3.3 Functions, Lambdas & Sections
- Named function:
  ```geisha
  pub def add(a: Int, b: Int): Int = a + b
  ```
- Lambda: `(x, y) -> x + y` or `x -> x + 1`.
- Operator sections / values: `(+)`, `(<|)` treat an infix operator as a first-class 2-argument function.
- Error propagation (`?`): `expr?` unwraps `Ok(v)` or early-returns `Err(e)` from the enclosing function returning `Result _ E`.

### 3.4 Data Construction & Field Projection
- Tuple: `(a, b, c)`
- List literal: `[1, 2, 3]`, empty `[]` or `Nil`
- Record construction: `Point { x: 1.0, y: 2.0 }`
- Static field projection: `p.x` (resolved statically by record type; Geisha does **not** use `obj.method()` syntax).

### 3.5 Operator Precedence & Associativity
Infix operators have 13 precedence levels (1 = lowest, 13 = highest). Operators ending in `:` are **right-associative**; all others are **left-associative**.

| Level | Operators / Leading Character |
| :---: | --- |
| 1 | Multi-char `\|`-leading pipelines (except `\|\|`) |
| 2 | `\|\|` (short-circuit logical OR) |
| 3 | `&&` (short-circuit logical AND) |
| 4 | `=`, `!`-leading equality (`==`, `!=`, `===`, ...) |
| 5 | `<`, `>`-leading comparisons & combinators (except shifts) |
| 6 | `:`-leading (e.g., `::`, right-associative) |
| 7 | `\|` (bitwise OR) |
| 8 | `^`-leading (bitwise XOR) |
| 9 | `&`-leading (bitwise AND, except `&&`) |
| 10 | Shifts: `<<`, `>>`, `>>>` |
| 11 | `+`, `-`-leading additive |
| 12 | `*`, `/`, `%`-leading multiplicative |
| 13 | `@`, `#`, `$`, multi-char `?`, multi-char `~`, `\` |

Unary prefix operators: `!` (logical NOT), `-` (negation), `~` (bitwise NOT).

---

## 4. Script Mode & Program Entry

Geisha supports two execution forms:
1. **Standard Module / Application**: Contains top-level `def main(): Void` (or `def main(): Int` / `Result _ _`).
2. **Script Mode**: Standalone `.gsa` files (including `#!/usr/bin/env -S geisha run`) or `geisha eval '<code>'` may contain top-level `let` bindings and statements directly without `def main()`.
   - `geisha run file.gsa [args...]` and `geisha eval` compile and cache executables under `~/.geisha/cache/scripts/` keyed by content hash and local import graph.

---

## 5. Type System & Hindley-Milner Inference

### 5.1 Primitive & Built-in Types
- **Scalars**: `Int`, `Int64`, `Float` (IEEE 754 `f64`), `Float32` (`f32`), `Bool`, `Char`, `String`, `Void` (`()`).
- **Mutable & Array Containers**: `Cell a`, `MutArray a` (legacy alias `Array a`), `ImmArray a`, `List a` (`Nil`, `Cons(a, List a)`).
- **FFI & Regions**: `Ptr`, `ForeignPtr`, `ScopedPtr`, `Arena`.
- **Concurrency**: `AtomicInt`, `MVar a`, `Chan a`, `Task a`, `Actor s`.
- **Generic Representation**: `Unit`, `Named a`, `Prod a b`, `Sum a b`.

### 5.2 Function Types & Capture Modes
Every function type carries an internal capture mode `m ∈ { $Shared, $Local, $Scoped }` (with subtyping `$Shared <: $Local <: $Scoped`):
- `$Shared`: Captures no mutable local state (`Cell`/`MutArray`/`Ptr`/`ForeignPtr`) and no scoped resources; satisfies `Send`.
- `$Local`: May capture `Cell`/`MutArray`/`ForeignPtr`; may escape its defining scope; `!Send`.
- `$Scoped`: Captures `ScopedPtr` or `Arena`; cannot escape its enclosing region (`withForeignPtr`, `withAlloca`, `withArena`) and cannot be stored in `Cell`/`MutArray`.

### 5.3 Algebraic Data Types & Type Aliases
```geisha
// Sum type with unit, tuple, and record variants
pub data Expr {
    ELit(Int),
    EAdd { lhs: Expr, rhs: Expr },
    EEmpty,
}

// Single-constructor record shorthand
pub data Point { x: Float, y: Float }

// Single-constructor tuple shorthand
pub data Wrapper a (a)

// Type alias
pub type StrPair = (String, String)
```
Parametric ADTs are kind-checked (`*`, `* -> *`, etc.) during inference.

---

## 6. Concepts, Instances & Generic Deriving

### 6.1 Concept Declarations
```geisha
pub concept Eq a {
    eq: (a, a) -> Bool
}

// Superclasses & functional dependencies
pub concept (Eq a) => Ord a {
    compare: (a, a) -> Int
}

pub concept Collect c e | c -> e {
    empty: () -> c,
    insert: (c, e) -> c,
}
```

### 6.2 Built-in Operator Concepts
Binary/unary operators desugar to open Concepts, allowing user types to overload them:
- Arithmetic: `Add` (`+`), `Sub` (`-`), `Mul` (`*`), `Div` (`/`), `Rem` (`%`), `Neg` (`neg`)
- Bitwise: `BitAnd` (`&`), `BitOr` (`|`), `BitXor` (`^`), `BitNot` (`~`), `Shl` (`<<`), `Shr` (`>>`), `Ushr` (`>>>`)
- Comparison: `Eq` (`eq`), `Ord` (`compare`)
- Concurrency: `Send a`, `SendIf m a`

### 6.3 Generic Deriving (Zero-Keyword)
Structural `Generic` representations (`Unit`, `Named`, `Prod`, `Sum`) are synthesized automatically by the compiler. Types can derive Concepts inline or via bodyless instances:
```geisha
pub data User : Eq, Show {
    name: String,
    age: Int,
}

// Or separately:
pub instance Eq User
```

### 6.4 Orphan Rule
In library packages, an `instance C T1 ... Tn` is valid **only if** the current package owns the Concept `C` or at least one of the head type constructors `T1 ... Tn`. Violations are rejected at load/check time.

---

## 7. Pattern Matching & Exhaustiveness

Supported patterns:
- Variable (`x`), Wildcard (`_`)
- Literal (`0`, `"hi"`, `'a'`, `true`, `()`)
- Tuple (`(a, b)`)
- Constructor (`Cons(h, t)`, `Some(v)`)
- Record (`Point { x, y }`, `EAdd { lhs, rhs }`)

The compiler runs **Maranget's pattern-matrix specialization algorithm** (`src/infer.gsa`) to reject non-exhaustive `match` expressions statically. Verified Core Geisha guarantees total elimination of `Trap.matchFailure` (see `formal/CoreGeisha/Exhaustive.lean`).

---

## 8. Modules, Visibility & Resolution

- **Path-as-Module**: No `mod.gsa` or `mod foo;` boilerplate is required. `use pkg.sub.mod.{sym1, sym2 as s2}` resolves `pkg/sub/mod.gsa` on demand.
- **Umbrella Modules**: `foo.gsa` may coexist with `foo/*.gsa`.
- **Inline Submodules**: `mod sub { ... }` is supported within a file.
- **Imports**:
  - `use foo.bar` — qualified import (`bar.sym`)
  - `use foo.bar.{a, b as c}` — selective import
  - `use foo.bar.*` or `open foo.bar` — glob import
- **Visibility**: Top-level declarations are private by default; prefix with `pub` (`pub def`, `pub data`, `pub type`, `pub concept`, `pub instance`, `pub use`) to export.
- **Hermetic Package Scoping**: Dependencies are resolved per-package by alias; transitive dependencies do not leak into a consumer's namespace.

---

## 9. Memory Model, Escape Analysis & Scoped Regions

### 9.1 Escape Analysis
Before codegen, `src/core.gsa` runs a **2-phase interprocedural escape analysis**. Non-escaping `Cell` allocations (including loop-local cells) are promoted to stack slots and freed on frame return, eliminating heap allocation and write barriers.

### 9.2 Generational Bitmap GC
Escaping heap objects are managed by `runtime/runtime/gc_bitmap.c`:
- **Nursery**: 256 KB thread-local allocation buffer (TLAB) with fast bump-pointer allocation; minor GC sweeps young objects.
- **Old Generation**: 31 segregated size classes (16 B to 4096 B) + size-classed large-object cache, with sticky-mark generational write barriers and major mark-sweep collection for cyclic old-gen graphs.
- **Exact Pointer Masks**: Every heap object carries an 8-byte header with a 40-bit exact pointer bitmap (`src/codegen.gsa`), preventing scalar values from being misinterpreted as pointers.
- **Runtime Controls**: `gcTrim()`, `gcSetThresholds(minor, major)`, `gcHeapLiveBytes()`, `gcExternalLiveBytes()`.

### 9.3 Scoped Regions (`ForeignPtr`, `ScopedPtr`, `Arena`)
- `ForeignPtr` wraps an unmanaged C allocation (`foreignPtrAlloc`, `foreignPtrNew`) tracked by GC finalizers and external-memory pressure.
- `withForeignPtr(fp, p -> ...)` borrows a `ScopedPtr` while keeping `fp` alive across the callback.
- `withAlloca(bytes, p -> ...)` allocates stack-scoped scratch memory.
- `withArena(arena -> ...)` provides bump-allocated scratch memory via `arenaAlloc(arena, bytes)`.
- The compiler's `NoScoped` constraint forbids `ScopedPtr`, `Arena`, or `$Scoped` closures from escaping their callback or being stored in `Cell`/`MutArray`.

---

## 10. Concurrency & `Send` Safety

### 10.1 Coinductive `Send` Rules
A type `T` is `Send` if:
- `T` is a scalar (`Int`, `Int64`, `Float`, `Float32`, `Bool`, `Char`, `String`, `Void`), `AtomicInt`, or `Actor s` (unconditionally `Send`!).
- `T` is `MVar a`, `Chan a`, `Task a`, or `ImmArray a` where `a` is `Send`.
- `T` is a tuple or ADT whose constructor fields are all `Send` (checked coinductively for recursive ADTs like `List a`).
- `T` is a function type with mode `$Shared`.

`Ptr`, `Cell a`, `MutArray a`, `ForeignPtr`, `ScopedPtr`, `Arena`, `$Local` closures, and `$Scoped` closures are **never `Send`**.

### 10.2 Concurrency Primitives
- **`std.task`**: Structured async tasks (`Task a`) and data-parallel `parTabulate(n, i -> f(i)): ImmArray a` (requires `Send a` and `$Shared` body).
- **`std.sync`**: `MVar a` (synchronized single-slot box), `Chan a` (MPMC channel), and `AtomicInt`.
- **`std.actor`**: `Actor s` encapsulates arbitrary `!Send` state `s` on a dedicated sequential mailbox thread. Initializers `() -> s` and message handlers `s -> r` must be `$Shared`, guaranteeing data-race freedom.

---

## 11. C FFI & Compilation Targets

### 11.1 Unified `extern` C ABI Surface
```geisha
// C import (no body) & typed indirect function pointer call
extern "strlen" def c_strlen(s: Ptr): Int64
extern ptr def call_imp(fn: Ptr, obj: Ptr, sel: Ptr): Ptr

// C ABI value struct
pub extern data CGPoint { x: Float, y: Float }

// Pure C ABI export (symmetric with import, distinguished by `= body`)
pub extern "my_c_add" def myAdd(a: Int, b: Int): Int = a + b

// Static constructor (`@llvm.global_ctors`)
extern init def registerRuntimeClasses(): Void = ()
```
- Multiple `extern` imports may alias the same C symbol (such as `"objc_msgSend"`) with distinct non-variadic signatures.
- `extern ptr [noalloc] def ...` invokes parameter 0 (`Ptr`) as a typed C function pointer.
- `extern ["sym"] def ... = body` emits a pure C ABI symbol without a trailing closure-environment parameter, automatically wrapped in `gc_host_enter`/`gc_host_leave`.
- `cFnPtr(fn)` obtains a C function pointer (`Ptr`) for an `extern` function or a top-level monomorphic Geisha function (synthesizing a C ABI callback trampoline).
- `extern data` enforces C ABI value-struct layout & calling conventions (ARM64 HFA / SysV AMD64 / `sret` / `byval`) across FFI boundaries.
- `extern init[(priority)] def ...` registers a `() -> Void` static constructor in `@llvm.global_ctors`.
- `ForeignPtr` parameters in `extern` calls can auto-borrow as `ScopedPtr` with compiler-inserted keep-alives.
- `gcHandleNew`, `gcHandleGet`, and `gcHandleFree` pin GC-managed values across C callbacks.

### 11.2 Targets
- `native` (default): Host executable, object file (`-c`), or static/shared library (`--no-main`, `--export <fn>`, `--boot-sym <sym>`).
- `wasm32`: Freestanding WebAssembly module (`--target=wasm32 -mbulk-memory -mnontrapping-fptoint`) linked against `wasm_rt.o`, with configurable `exports` and `web_assets`.
- `ios` / `ios-sim`: ARM64 iOS device (`arm64-apple-ios16.0`) and simulator (`arm64-apple-ios16.0-simulator`) static archives (`libgeisha_runtime_ios.a` / `libgeisha_runtime_ios_sim.a`) for embedding into Xcode/Swift hosts.
- `macos-app` / `ios-app` / `ios-sim-app`: Native Apple `.app` and `.appex` bundles configured via `[target.macos]` / `[target.ios]` in `geisha.toml` (with `Info.plist`, frameworks, resources, nested `PlugIns/*.appex`, and `codesign`).

---

## 12. Package Management (`geisha.toml` & MVS)

### 12.1 Manifest (`geisha.toml`)
```toml
name = "my_app"
version = "0.1.0"
# entry = "src/main.gsa"
# src_dir = "src"
# tests = ["tests/extra.gsa"]
# benches = ["benches/core.gsa"]

[deps]
crema = { git = "github.com/geisha-lang/crema", version = "0.1.0" }
local_lib = { path = "../local_lib" }

[target.native]
c_sources   = ["native/shim.c"]
c_flags     = ["-O2"]
link_flags  = ["-lm"]
exports     = ["app_init"]
owns_main   = false
boot_symbol = "my_app_boot"

[[target.native.when]]
os         = "linux"          # optional: host OS match
tool       = "nvcc"           # optional: `command -v` check (or GEISHA_DISABLE_TOOL)
pkg_config = "sdl2"           # optional: injects --cflags / --libs
compiler   = "nvcc"           # optional: custom compiler for this unit's c_sources
c_sources  = ["native/kernel.cu"]
c_flags    = ["-O3"]
link_flags = ["-lcudart"]
defines    = ["USE_CUDA=1"]

[target.wasm32]
exports    = ["app_init", "app_step"]
web_assets = ["host/web/runtime.js"]
```

### 12.2 Resolution, Caching & Overrides
- **MVS**: Selects the minimum version satisfying all dependency constraints across the graph.
- **Global Cache**: Treeless bare clones and content-addressed package snapshots live in `~/.geisha/cache/p/<name>-<ver>-<sha256_12>/`.
- **Lockfile**: `geisha.lock` records exact `[[pkg]]` entries (`name`, `url`, `subdir`, `version`, `rev`, `sha256`).
- **Index**: Optional `$GEISHA_INDEX` static Git index maps short package names to Git URLs.
- **Local Overrides**: Untracked `geisha.local.toml` supports `[overrides]` (`"github.com/org/repo" = { path = "../repo" }`) as well as machine-local `[target.macos]`, `[target.ios]`, `[target.native]`, and `[target.wasm32]` overrides (e.g. local `codesign` certificates or SDK flags) without modifying `geisha.toml` or `geisha.lock`.

---

## 13. Compiler Diagnostics & Agent Tooling

- `geisha check [file.gsa] [--json]`: Runs lex, parse, load, HM inference, exhaustiveness, and `Send` checks without invoking LLVM/clang. Diagnostics use compact 1D `file:line:col: error[kind]: ...` + `near:` + `line N:` + `hint:`.
- `geisha doc [module|file] [--all]`: Prints public signatures and `///` doc comments for `std.*`, `sys.*`, and project/dependency modules.
- `geisha bench [file.gsa|filter] [--iters N] [--warmup N] [--rounds N] [--filter <pat>] [--json]`: Runs microbenchmarks in project mode (`benches/*.gsa`, `benches = [...]`, or `bench_*` functions) or standalone script mode using `std.bench` (`blackBox` polymorphic optimization barrier, warmup + multi-round stats).
- `geisha guide`: Prints the built-in [`AGENT_GUIDE.md`](../AGENT_GUIDE.md).
- `geisha lsp [--stdio]`: Starts the built-in JSON-RPC 2.0 Language Server over stdio (live diagnostics, hover with inferred types and `///` docs, go-to-definition, document symbols, and completion).
- `geisha build --dump-core <file.gscore>`: Emits Core Geisha S-expressions for translation validation against the Lean 4 checker (`make verify-core`).
