# Geisha Language — Agent Quick Reference (`geisha guide`)

Geisha (`.gsa`) is a statically typed, Hindley-Milner functional-imperative language with open Concepts/Instances, algebraic data types, exhaustive pattern matching, GC + `$Scoped` regions, `Send`-checked concurrency, and a decentralized Git/MVS package manager (`geisha.toml`), compiling to LLVM 20 IR (`native` on Linux, macOS, and Windows `x86_64-pc-windows-msvc`, `wasm32`, `ios`, `ios-sim`), native WebAssembly GC (`wasm-gc`, zero linear-memory GC runtime + companion `.mjs`/`.d.ts`), and zero-dependency ES Module JavaScript + TypeScript `.d.ts` (`js`).

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
   - `geisha run [--watch | -w] [--dev | --release] [--no-cache] [file.gsa] [args...]` — build & run project, or run a standalone `.gsa` script (content-hashed cache in `~/.geisha/cache/scripts/`; tracks local imports automatically; `--` before args is optional; `--watch` clears the screen and re-runs incrementally when `.gsa` or `geisha.toml` changes)
   - `geisha eval '<code>' [args...]` — evaluate an inline Geisha snippet (cached)
   - **Script mode**: standalone entry files support Unix shebang (`#!/usr/bin/env -S geisha run`) and top-level statements (`let` / expressions) without needing an explicit `def main()`
   - `geisha test [--watch | -w] [--dev | --release | --opt 0|1|2|3|s|z | -O<lvl>] [--single-cgu] [--no-cache]` (defaults to `--opt 0` / `--dev` and shares `-O0` CGU & C `.o` caches with `geisha build --dev`; `geisha test --release` shares `-O2` caches with default `geisha build`; `--watch` watches `.gsa` & `geisha.toml` for incremental re-runs)
   - `geisha bench [file.gsa|filter] [--iters N] [--warmup N] [--rounds N] [--filter <pat>] [--json]` — run microbenchmarks in project mode (`benches/*.gsa`, `benches = [...]` in `geisha.toml`, or `bench_*` functions) or standalone script mode (outputs mean/median/min/max/ops/sec, with `--json` for CI/Agent regression tracking)
   - `geisha fmt [--check] [--write] [--stdout] [paths...]` — format `.gsa` files in-place (defaults to project/cwd; `--check` exits non-zero if any file needs formatting; `--stdout` prints formatted output)
   - `geisha build [--target native|wasm32|wasm-gc|js|ios|ios-sim|macos-app|ios-app|ios-sim-app] [-g|--debug] [-O0..-O3|-Os|-Oz|--opt[=]<lvl>|--dev|--release] [--strip] [--slim-runtime] [--no-dts] [--single-cgu] [--no-cache] [-o out]` (splits multi-module programs into per-module LLVM CGUs compiled in parallel with content-addressed `.o` caching in `build/cache/cgu/` and `build/cache/native/`; override concurrency via `GEISHA_JOBS`)
   - **Source-level debugging (`lldb` / `gdb` / VS Code CodeLLDB)**: compile with `-g` / `--debug` (defaults to `-O0`, disables tail-call optimization, emits DWARF v4 line info + `@llvm.dbg.declare` local variables, and runs `dsymutil` on macOS). Load `~/.geisha/lib/geisha_lldb.py` in LLDB for formatted `String`, `Vec`, `Array`, `List`, `Option`, and boxed ADT inspection (see `docs/DEBUGGING.md`).
   - `geisha init [--lib] [dir]` / `geisha add <pkg|git-url>` / `geisha remove <alias>` / `geisha fetch` / `geisha update`
5. **Editor / IDE integration (LSP)**:
   - `geisha lsp` — start the built-in JSON-RPC 2.0 Language Server over stdio (diagnostics, hover with inferred types & `///` docs, go-to-definition, find references, scope-aware rename with `prepareRename`, inlay hints for inferred `let` types & call parameter names, quick-fix code actions, document symbols, completion)

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
- Types: `Int` (32-bit signed int `-2147483648..2147483647`, checked at parse time; literals support decimal `1_000_000`, hex `0xFF_00`, octal `0o600`, and binary `0b1010_0101`), `Int64`, `Float` (f64, supports `_` separators like `1_000.5`), `Float32`, `Bool`, `Char`, `String`, `Void` (`()`), `Ptr`, `ForeignPtr`, `ScopedPtr`, `Cell a`, `Array a`, `ImmArray a`, `List a` (`Nil`, `Cons(h, t)`).
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
- All C ABI boundaries share the single `extern` keyword (zero `@` attributes):
  - **C import**: `extern [noalloc] ["c_sym"] def fn(x: Int): Ptr` (multiple typed declarations may alias the same symbol such as `"objc_msgSend"`); `ForeignPtr` auto-borrows as `ScopedPtr` at `extern` boundaries with compiler keep-alive.
  - **Indirect C function pointer call**: `extern ptr [noalloc] def call_fp(fp: Ptr, ...): Ret` invokes parameter 0 (`Ptr`) with exact C ABI signature.
  - **Pure C ABI export**: `pub extern ["c_sym"] def fn(x: Int): Int = ...` (symmetric with import, distinguished by `= body`; omits trailing `%fvs` closure param and wraps in `gc_host_enter`/`gc_host_leave`).
  - **C ABI value struct**: `pub extern data CGPoint { x: Float, y: Float }` enforces C ABI struct layout & calling convention (ARM64 HFA / SysV AMD64 / Win64 x64 / `sret` / `byval`).
  - **Static constructor**: `extern init[(priority)] def setup(): Void = ...` emits `@llvm.global_ctors` (e.g. registering Objective-C subclasses before `main`/`NSExtensionMain`).
  - **C function pointer / callback**: `cFnPtr(fn)` returns `Ptr` for an `extern` function or synthesizes a thread-safe C ABI callback trampoline for a monomorphic top-level Geisha function.

---

## 4. Standard Library Quick Index

Run `geisha doc <module>` to get exact public signatures before using any module.

### `std.*`
- `std.option` — `Option a` (`Some`, `None`) and helpers
- `std.result` — `Result a e` (`Ok`, `Err`) and helpers
- `std.list` — singly-linked `List a` (`listLen`, `listRev`, `listAppend`, ...)
- `std.control` — higher-order combinators (`fmap`, ...)
- `std.bits` — bitwise utilities
- `std.path` — host-OS-aware path manipulation (`isAbsPath`, `pathJoin`, `pathDirname`, `pathBasename`, `pathStem`, `pathWithExt`) plus explicit Windows-style `*Win` variants (`isAbsPathWin`, `pathJoinWin`, `pathDirnameWin`, `pathBasenameWin`, `pathStemWin`, `pathWithExtWin`)
- `std.char` — ASCII/byte classification (`isDigitByte`, `isUpperByte`, `isLowerByte`, ...)
- `std.buf` — mutable `StringBuf` (`bufNew`, `bufPushStr`, `bufPushByte`, `bufToString`)
- `std.str` — string & numeric utilities (`intToStr`, `i64ToStr`, round-trip `floatToStr`, overflow-checked `parseInt` / `parseInt64`, `parseFloat`, `strJoin`, `strSplitChar`, `strStartsWith`, `strEndsWith`, `strIndexOfByte`, ...)
- `std.vec` — growable `Vec a` (`vecNew`, `vecPush`, `vecLen`, `vecGetOr`, ...)
- `std.map` — hash maps `StrMap v` & `IntMap v` (`strMapNew`, `strMapGet`, `strMapInsert`, `intMapNew`, `intMapGet`, `intMapInsert`, ...)
- `std.sync` — mutexes, channels, atomics
- `std.task` — structured concurrency tasks & parallel execution
- `std.actor` — typed message-passing actors
- `std.rand` — pseudo-random number generation
- `std.math` — floating-point math (`sin`, `cos`, `exp`, `log`, `sqrt`, ...)
- `std.generic` — `Generic` representation (`Rep`, `toRep`, `fromRep`) for zero-keyword deriving
- `std.codec` — binary/text encoding & decoding concepts
- `std.json` — JSON parser, AST, and serializer
- `std.toml` — TOML parser, canonical serializer, and comment-preserving `patch`
- `std.sha256` — SHA-256 hashing
- `std.bench` — microbenchmarking (polymorphic `blackBox`, `blackBoxBarrier`, `BenchConfig`, `BenchStats`, `measure`, `bench`, `benchWith`, `benchGroup`, `formatStatsText`, `formatStatsJson`, `formatStatsJsonInFile`)

### `sys.*`
- `sys.io` — stdout/stderr/stdin (`eprintLn`, ...)
- `sys.fs` — files, directories, atomic writes, permissions/mtime, and zero-copy `Mmap` (`readFile`, `writeFile`, `writeFileAtomic`, `writeFileAtomicMode`, `renameFile`, `chmod`, `fileMtimeMs`, `fileExists`, `isDir`, `mkdirAll`, `readDir`, `removeFile`, `removeDir`, `removeDirAll`, `withMmap`)
- `sys.env` — CLI args and env vars (`argCount`, `argAt`, `getEnv`)
- `sys.proc` — structured subprocesses, pipes, timeouts, signals, and decoded-exit-code shell execution (`Command`, `command`, `spawn`, `run`, `runTimeout`, `childSignal`, `Pipe`, `exit`, `shell`)
- `sys.time` — monotonic/wall clock and sleep
- `sys.net` — TCP/UDP networking sockets
- `sys.ffi` — dynamic library loading (`dlOpen`, `dlOpenSelf`, `dlSym`, `dlClose`, `ptrToStrOpt`)

---

## 5. Package Manifest (`geisha.toml`)

```toml
name = "my_app"
version = "0.1.0"
# entry = "src/main.gsa"   # optional; defaults to src/main.gsa or src/<name>.gsa
# src_dir = "src"
# benches = ["benches/bench_core.gsa"]  # optional; defaults to benches/*.gsa or bench_* in src/

[deps]
crema = { git = "github.com/geisha-lang/crema", version = "0.1.0" }
local_lib = { path = "../local_lib" }
# `geisha add` may emit `url_encoding = "pct"` on percent-encoded `file://` Git deps to disambiguate them from legacy unencoded v1 `file://` entries.

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
exports      = ["app_init", "app_step"]
web_assets   = ["host/web/runtime.js"]
opt          = "z"        # "0" | "1" | "2" (default) | "3" | "s" | "z" (defaults strip = true on s/z, runs optional wasm-opt unless GEISHA_DISABLE_TOOL=wasm-opt)
strip        = true       # strip custom/name sections (set false to keep names even under opt = "z")
slim_runtime = false      # true omits default gs_wasm_* bridge exports so --gc-sections drops unused GC

[target.wasm-gc]
exports      = ["add", "parseDoc"]
web_assets   = ["host/web/index.html"]
dts          = true       # emit companion .d.ts alongside .wasm + .mjs glue (default: true)
owns_main    = false      # true skips auto-invoking main() in companion .mjs glue

[target.js]
exports      = ["add", "parseDoc"]
web_assets   = ["host/web/index.html"]
dts          = true       # emit companion .d.ts TypeScript declarations (default: true)
owns_main    = false      # true skips auto-invoking main() on module import

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
extension_point = "com.apple.keyboard-service"
principal_class = "MyViewCtrl"   # used when `is_extension = true`
codesign        = "-"
```
- Local overrides without touching `geisha.toml` or `geisha.lock`: put `[overrides]` or machine-local `[target.macos]` / `[target.ios]` / `[target.native]` settings (e.g. local `codesign` identity) in an untracked `geisha.local.toml`.
- **Windows (`x86_64-pc-windows-msvc`)**: Native Windows builds use LLVM/Clang + LLD + MSVC UCRT (`make runtime wasm-runtime bootstrap && make test` under Git Bash / MSYS2 with `clang`, `llvm-ar`, `wasm-ld`, and GNU `make`), emit `.exe` binaries automatically, link `-lws2_32 -lbcrypt`, and support full UTF-8 paths/argv/env, Win64 C ABI, Winsock2 TCP, Job Object process groups, and `.zip` release bundles (`make dist`).
