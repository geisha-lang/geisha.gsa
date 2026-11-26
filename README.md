# geisha.gsa

Self-hosting compiler and decentralized package manager for the **Geisha** programming language, written in Geisha and targeting **LLVM 20 opaque-pointer IR** (`native` & `wasm32`).

## Architecture

`geisha.gsa` implements the complete Geisha language pipeline and zero-server package manager in pure Geisha (`src/`) linked with a small portable C11 runtime (`runtime/`):

| Module | Responsibility |
| --- | --- |
| `src/ast.gsa` | Core AST, Hindley-Milner `Type`/`Scheme`, patterns, module items, and 15-level Scala/Swift-style operator precedence table |
| `src/lexer.gsa` | Linear-time tokenizer with newline tracking (`hadNewline`), nested block comments, escapes, and custom symbolic operators |
| `src/parser.gsa` | Recursive-descent + Pratt expression parser, `(op)` operator sections, destructuring `let`, and `Result` early-return `?` desugaring |
| `src/stdlib_bundle.gsa` | Embedded `std.*` and `sys.*` standard library sources (including `std.codec`, `std.json`, `std.toml`, and `std.sha256`, generated from `stdlib/` via `scripts/gen_stdlib.py`) |
| `src/loader.gsa` | Path-as-module demand-driven `use`/`open` loader (no `mod.gsa` or `mod` lists needed), sibling umbrella modules (`foo.gsa` + `foo/*.gsa`), hermetic package-scoped dependencies, and cross-package Concept/Instance Orphan Rule checking |
| `src/infer.gsa` | Hindley-Milner type inference, open Concepts & Instances (including arithmetic/comparison/bitwise operator overloading), `Send` checking, `.field` resolution, mutual recursion backfill, and Maranget exhaustiveness checking |
| `src/core.gsa` | K-conversion, polymorphic local lambda lifting, deterministic closure conversion, demand-driven worklist monomorphization, static Concept dispatch, concurrent closure `Send` verification, and 2-phase interprocedural escape analysis |
| `src/codegen.gsa` | Static LP64 / Wasm32 ABI layout calculator and LLVM 20 opaque-pointer textual IR (`.ll`) emitter |
| `src/pkg.gsa` | Zero-server Git/MVS package manager (`geisha.toml`, `geisha.local.toml`, `geisha.lock`), content-addressed global cache (`~/.geisha/cache`), and declarative native/wasm32 C/ObjC & web asset builder |
| `src/geisha.gsa` | Unified CLI entry point (`init`, `add`, `remove`, `fetch`, `update`, `build`, `run`, `test`, plus direct compiler flags) |

## Bootstrapping & Fixed-Point Verification

Run the 3-stage bootstrap and verify the fixed point (`stage2.ll == stage3.ll`):

```sh
make bootstrap STAGE0=/path/to/previous/geisha
```

Install the self-hosted toolchain (`geisha`, `libgeisha_runtime.a`, `wasm_rt.o`) to `~/.geisha`:

```sh
make install
```

Run the end-to-end language & package manager test suite:

```sh
make test
```

## Decentralized Package Manager (`geisha.toml`)

Geisha requires **no centralized registry server**: packages are addressed directly by Git URLs (or short names via a static Git index `$GEISHA_INDEX`), resolved deterministically with **Minimal Version Selection (MVS)** over treeless bare clones (`--filter=blob:none`), and pinned with SHA-256 content hashes in `geisha.lock`:

```toml
# geisha.toml
name = "my_app"
version = "0.1.0"

[deps]
kagura = { git = "github.com/geisha-lang/kagura", version = "0.1.0" }

[target.native]
c_sources  = ["host/native/macos_host.m"]
c_flags    = ["-fobjc-arc"]
link_flags = ["-framework", "Cocoa", "-framework", "QuartzCore"]
exports    = ["app_init", "app_step"]
owns_main  = true

[target.wasm32]
exports    = ["app_init", "app_step"]
web_assets = ["host/web/runtime.js"]
```

```sh
# Initialize a binary or library project (creates geisha.toml + src/main.gsa)
geisha init my_app
geisha init --lib my_lib

# Add dependencies by Git URL, owner/repo shorthand, short index name, or local path
geisha add github.com/geisha-lang/kagura
geisha add kagura --path ../kagura

# Build, run, and test (offline once cached in ~/.geisha/cache/p/)
geisha build
geisha build --target wasm32
geisha run
geisha test
```

For multi-repo local development without touching `geisha.toml` or `geisha.lock`, place an untracked `geisha.local.toml` in the project root:

```toml
[overrides]
"github.com/geisha-lang/kagura" = { path = "../kagura" }
```
