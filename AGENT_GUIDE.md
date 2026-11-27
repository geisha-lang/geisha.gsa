# Geisha Language — Agent Quick Reference (`geisha guide`)

Geisha (`.gsa`) is a statically typed, Hindley-Milner functional-imperative language with open Concepts/Instances, algebraic data types, exhaustive pattern matching, GC + `$Scoped` regions, `Send`-checked concurrency, and a decentralized Git/MVS package manager (`geisha.toml`), compiling to LLVM 20 IR (`native`, `wasm32`, `ios`, `ios-sim`).

## 1. Agent Workflow (Use These First!)

1. **Read this guide**: `geisha guide`
2. **Inspect APIs before calling them (zero hallucination)**:
   - `geisha doc` — list all built-in `std.*` / `sys.*` modules + current project modules/deps
   - `geisha doc std.str` — print public types, concepts, instances, and function signatures of `std.str`
   - `geisha doc path/to/file.gsa [--all]` — inspect any local file or dependency module
3. **Fast typecheck loop (no LLVM/clang link)**:
   - `geisha check` — check current `geisha.toml` project
   - `geisha check file.gsa [--json]` — check a single file (optional `--json` output)
4. **Run, script, test, build**:
   - `geisha run [file.gsa] [args...]` — build & run project, or run a standalone `.gsa` script (content-hashed cache in `~/.geisha/cache/scripts/`; tracks local imports automatically; `--` before args is optional)
   - `geisha eval '<code>' [args...]` — evaluate an inline Geisha snippet (cached)
   - **Script mode**: standalone entry files support Unix shebang (`#!/usr/bin/env -S geisha run`) and top-level statements (`let` / expressions) without needing an explicit `def main()`
   - `geisha test`
   - `geisha build [--target native|wasm32|ios|ios-sim|macos-app|ios-app|ios-sim-app] [-o out]`
   - `geisha init [--lib] [dir]` / `geisha add <pkg|git-url>` / `geisha remove <alias>` / `geisha fetch` / `geisha update`

---

## 2. Top LLM Pitfalls (Anti-Patterns to Avoid)

| ❌ Habit from Rust / OCaml / Haskell / Swift | ✅ Correct Geisha Syntax |
| --- | --- |
| `let mut x = 0; x = x + 1` | `let x = cellNew(0); cellSet(x, cellGet(x) + 1)` |
| `fn add(a: Int, b: Int) -> Int { a + b }` | `def add(a: Int, b: Int): Int = a + b` |
| `if x > 0 { 1 } else { 0 }` | `if (x > 0) { 1 } else { 0 }` (parens around condition required) |
| `if (cond) { doThing() }` (missing `else`) | `if (cond) { doThing() } else ()` (`else` is always required) |
| `while i < n { ... }` | `while (cellGet(i) < n) { ... }` (parens required) |
| `match opt { Some(v) => v, None => 0 }` | `match opt { Some(v) -> v, None -> 0 }` (`->` not `=>`) |
| `\|x, y\| x + y` or `\x -> x` | `(x, y) -> x + y` |
| `x.len()` / `v.push(1)` (method call) | `strLen(x)` / `vecPush(v, 1)` (`.field` is for record fields only) |
| `s[0]` (string indexing) | `strByteAt(s, 0)` (returns ASCII/byte `Int`), `strSlice(s, a, b)` |
| `x :: xs` / `[]` | `Cons(x, xs)` / `Nil` (list literals `[1, 2, 3]` work; empty is `Nil` or `[]`) |
| Trailing `;` on final block expression `{ a; b; }` | `{ a; b }` (`;` separates statements; last item in `{ ... }` must be an expression with no trailing `;`) |
| Creating `mod.gsa` or `mod foo;` boilerplate | Path-as-module: just write `use foo.bar.{baz}` and place `foo/bar.gsa` |
| `return Err(e)` | Early return only via `?` on `Result`; otherwise `if`/`match` expressions |

---

## 3. Core Syntax & Semantics

### Primitives & Built-ins
- Types: `Int` (32/64-bit platform int), `Int64`, `Float` (f64), `Float32`, `Bool`, `Char`, `String`, `Void` (`()`), `Ptr`, `ForeignPtr`, `ScopedPtr`, `Cell a`, `Array a`, `ImmArray a`, `List a` (`Nil`, `Cons(h, t)`).
- Built-in primitives (no import needed): `printLn`, `strLen`, `strByteAt`, `strSlice`, `strConcat`, `ptrSliceFromStr`, `ptrSliceToString`, `ptrIsNull`, `ptrNull`, `ptrToString`, `ptrAllocBytes`, `ptrByteAt`, `cellNew`, `cellGet`, `cellSet`, `arrayNew`, `arrayGet`, `arraySet`, `arrayLen`, `intToI64`, `i64ToInt`, `parTabulate`.
- Operators: `+`, `-`, `*`, `/` (works on `Int`, `Float`, `Float32`, and `String` concatenation via `+`), `%`, `==`, `!=`, `<`, `<=`, `>`, `>=`, `&&`, `||`, `!`, `&`, `|`, `^`, `<<`, `>>`, `>>>`, `~`. Custom symbolic operators can be defined with `def (<op>)(a, b) = ...`.

### Functions, Bindings & Control Flow
```geisha
pub def factorial(n: Int): Int =
    if (n <= 1) 1 else n * factorial(n - 1)

def sumTo(n: Int): Int = {
    let acc = cellNew(0);
    let i = cellNew(1);
    while (cellGet(i) <= n) {
        cellSet(acc, cellGet(acc) + cellGet(i));
        cellSet(i, cellGet(i) + 1)
    };
    cellGet(acc)
}
```
- Destructuring `let`: `let (a, b) = pair;` and `let Point { x, y } = p;`.
- `?` operator: unwraps `Ok(v)` or early-returns `Err(e)` inside a function returning `Result _ E`.
- Pattern guards: `Some(x) if (x > 0) -> x`.

### Algebraic Data Types, Records & Generic Deriving
```geisha
// Sum type (variants can be unit, tuple, or named record)
pub data Expr {
    ELit(Int),
    EAdd { lhs: Expr, rhs: Expr },
    EEmpty,
}

// Single-constructor record & tuple shorthands
pub data Point { x: Float, y: Float }
pub data Wrapper a (a)

// Zero-keyword Generic deriving via `: Concept1, Concept2`
pub data User : Eq, Show {
    name: String,
    age: Int,
}
// Or bodyless instance for a Generic-derived concept:
pub instance Eq User

// Type alias
pub type StrPair = (String, String)
```
- Field access: `p.x` (resolved statically by type).
- Pattern matching is checked for exhaustiveness (Maranget algorithm).

### Concepts & Instances (Typeclasses)
```geisha
pub concept Show a {
    show: a -> String
}

pub instance Show Int {
    def show(x: Int): String = intToStr(x)
}

// Constrained polymorphic function
pub def printShow(x: a): Void = ... // or with explicit scheme:
// Multi-param concepts support functional dependencies (`| a b -> c`)
```
- Arithmetic/comparison/bitwise operators are backed by open Concepts (`Add`, `Sub`, `Mul`, `Div`, `Eq`, `Ord`, etc.).
- **Orphan Rule**: In library packages, an `instance Concept Type` must be defined in the package that defines either `Concept` or `Type`.

### Modules & Imports
- **Path-as-module**: `use pkg.sub.mod.{sym1, sym2 as s2}` loads `pkg/sub/mod.gsa` on demand (no `mod.gsa` required).
- `use foo.bar` imports `bar` qualified; `use foo.bar.*` or `open foo.bar` imports all public symbols.
- Visibility: top-level items are private by default; prefix with `pub` to export (`pub def`, `pub data`, `pub type`, `pub concept`, `pub instance`, `pub use`).

### Concurrency & FFI
- `Send` concept is checked statically by the compiler for closures/values crossing thread boundaries (`std.task`, `std.actor`, `std.sync`).
- `extern "c_symbol" def c_fn(x: Int): Ptr` binds C ABI functions (multiple typed declarations may alias the same symbol such as `"objc_msgSend"`); `extern ptr def call_fp(fp: Ptr, ...): Ret` invokes a typed C function pointer indirectly; `ForeignPtr` auto-borrows as `ScopedPtr` at `extern` boundaries with compiler keep-alive.
- **Pure C ABI Exports, Callbacks, Structs & Static Constructors**:
  - `@export` / `@export("c_sym")` on a monomorphic top-level `def` emits a pure C ABI symbol (no trailing `%fvs` closure param, wrapped in `gc_host_enter`/`gc_host_leave`).
  - `cFnPtr(fn)` returns a C function pointer (`Ptr`) for a top-level Geisha function (synthesizing a thread-safe C callback trampoline) or an `extern` function (e.g. `cFnPtr(c_free)`).
  - `@cstruct` on a single-constructor non-recursive `data` type enforces C ABI value-struct layout & calling convention (ARM64 HFA / SysV AMD64 / `sret` / `byval`, e.g. `CGPoint`, `CGRect`).
  - `@ctor` / `@ctor(priority)` on a `() -> Void` top-level `def` registers a static constructor (`@llvm.global_ctors`), e.g. for registering Objective-C subclasses before `main`/`NSExtensionMain`.

---

## 4. Standard Library Quick Index

Run `geisha doc <module>` to get exact public signatures before using any module.

### `std.*`
- `std.option` — `Option a` (`Some`, `None`) and helpers
- `std.result` — `Result a e` (`Ok`, `Err`) and helpers
- `std.list` — singly-linked `List a` (`listLen`, `listRev`, `listAppend`, ...)
- `std.control` — higher-order combinators (`fmap`, ...)
- `std.bits` — bitwise utilities
- `std.path` — path manipulation (`pathJoin`, `pathDirname`, `pathBasename`, `pathStem`, ...)
- `std.char` — ASCII/byte classification (`isDigitByte`, `isUpperByte`, `isLowerByte`, ...)
- `std.buf` — mutable `StringBuf` (`bufNew`, `bufPushStr`, `bufPushByte`, `bufToString`)
- `std.str` — string utilities (`intToStr`, `parseInt`, `parseFloat`, `strJoin`, `strSplitChar`, `strStartsWith`, `strEndsWith`, `strIndexOfByte`, ...)
- `std.vec` — growable `Vec a` (`vecNew`, `vecPush`, `vecLen`, `vecGetOr`, ...)
- `std.map` — hash map `StrMap v` (`strMapNew`, `strMapGet`, `strMapInsert`, `strMapContains`, ...)
- `std.sync` — mutexes, channels, atomics
- `std.task` — structured concurrency tasks & parallel execution
- `std.actor` — typed message-passing actors
- `std.rand` — pseudo-random number generation
- `std.math` — floating-point math (`sin`, `cos`, `exp`, `log`, `sqrt`, ...)
- `std.generic` — `Generic` representation (`Rep`, `toRep`, `fromRep`) for zero-keyword deriving
- `std.codec` — binary/text encoding & decoding concepts
- `std.json` — JSON parser, AST, and serializer
- `std.toml` — TOML parser and AST
- `std.sha256` — SHA-256 hashing

### `sys.*`
- `sys.io` — stdout/stderr/stdin (`eprintLn`, ...)
- `sys.fs` — files, directories, and zero-copy `Mmap` (`readFile`, `writeFile`, `fileExists`, `isDir`, `mkdirAll`, `readDir`, `removeFile`, `withMmap`)
- `sys.env` — CLI args and env vars (`argCount`, `argAt`, `getEnv`)
- `sys.proc` — process exit and shell execution (`exit`, `shell`)
- `sys.time` — monotonic/wall clock and sleep
- `sys.net` — TCP/UDP networking sockets
- `sys.ffi` — dynamic library loading (`dlOpen`, `dlOpenSelf`, `dlSym`, `dlClose`, `ptrToStrOpt`)
- `sys.objc` — native Objective-C Runtime & Apple Blocks ABI (`Id a`, `objcClass`, `objcSel`, `withAutoreleasePool`, `nsString`, `fromNSString`, `objcAllocateClass`, `objcAddMethod`, `objcRegisterClass`, `objcSetAssocHandle`, `objcBlock0`/`objcBlock1Ptr`/`objcBlock2Ptr`/`objcBlock1Bool`/`objcBlockCustom`, typed `msgSend*`)

---

## 5. Package Manifest (`geisha.toml`)

```toml
name = "my_app"
version = "0.1.0"
# entry = "src/main.gsa"   # optional; defaults to src/main.gsa or src/<name>.gsa
# src_dir = "src"

[deps]
crema = { git = "github.com/geisha-lang/crema", version = "0.1.0" }
local_lib = { path = "../local_lib" }

[target.native]
c_sources  = ["native/shim.c"]
c_flags    = ["-O2"]
link_flags = ["-lm"]
exports    = ["app_init"]
owns_main  = false

# Conditional native compilation rules (os, tool, pkg_config, compiler, defines)
[[target.native.when]]
tool      = "nvcc"
compiler  = "nvcc"
c_sources = ["native/kernel.cu"]
defines   = ["USE_CUDA=1"]

[target.wasm32]
exports    = ["app_init", "app_step"]
web_assets = ["host/web/runtime.js"]

# Native Apple `.app` / `.appex` bundle targets (`macos-app`, `ios-app`, `ios-sim-app`)
[target.macos]
bundle_id    = "com.example.myapp"
bundle_name  = "MyApp"
min_os       = "14.0"
frameworks   = ["Cocoa", "QuartzCore"]
lsui_element = false
codesign     = "-"

[target.ios]
bundle_id       = "com.example.myapp"
bundle_name     = "MyApp"
min_os          = "16.0"
frameworks      = ["UIKit", "Foundation", "QuartzCore"]
is_extension    = false          # true => builds `.appex` with `-fapplication-extension -e _NSExtensionMain`
principal_class = "MyViewCtrl"   # used when `is_extension = true`
codesign        = "-"
```
- Local overrides without touching `geisha.toml` or `geisha.lock`: put `[overrides]` in an untracked `geisha.local.toml`.
