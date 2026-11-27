# Packages, Targets & FFI Interop

This document covers Geisha's decentralized Git/MVS package manager (`geisha.toml`), local overrides (`geisha.local.toml`), conditional native builds, and cross-compilation to `wasm32`, `ios`, and `ios-sim`.

---

## 1. Package Manifest (`geisha.toml`)

A minimal `geisha.toml`:

```toml
name = "my_app"
version = "0.1.0"
# entry = "src/main.gsa"   # Optional; defaults to src/main.gsa or src/<name>.gsa
# src_dir = "src"          # Optional; defaults to "src"
```

### Dependencies (`[deps]`)

Packages are identified by Git URLs, `owner/repo` shorthands, short names (via `$GEISHA_INDEX`), or local filesystem paths:

```toml
[deps]
crema    = { git = "github.com/geisha-lang/crema", version = "0.1.0" }
subpkg    = { git = "github.com/org/monorepo", subdir = "packages/sub", rev = "main" }
local_lib = { path = "../local_lib" }
```

CLI commands:
```sh
geisha add github.com/geisha-lang/crema --version 0.1.0
geisha add ../local_lib --as my_local
geisha remove my_local
geisha fetch     # Materialize dependencies into ~/.geisha/cache
geisha update    # Re-resolve remote tags/revs and update geisha.lock
```

### Minimal Version Selection (MVS) & `geisha.lock`

- Geisha uses **MVS** over treeless bare clones (`git clone --filter=blob:none`).
- Resolved packages are stored content-addressed in `~/.geisha/cache/p/<name>-<ver>-<sha256_12>/`.
- `geisha.lock` pins every `[[pkg]]` with `name`, `url`, `subdir`, `version`, `rev`, and `sha256`. Commit `geisha.lock` for reproducible builds.

### Local Overrides (`geisha.local.toml`)

During multi-repo development, create an untracked `geisha.local.toml` (automatically ignored by `geisha init`'s `.gitignore`):

```toml
[overrides]
"github.com/geisha-lang/crema" = { path = "../crema" }
```

---

## 2. Native Target & C/ObjC/CUDA Interop (`[target.native]`)

```toml
[target.native]
c_sources   = ["host/native/macos_host.m"]
c_flags     = ["-fobjc-arc", "-O2"]
link_flags  = ["-framework", "Cocoa", "-framework", "QuartzCore"]
exports     = ["app_init", "app_step"]
owns_main   = true
boot_symbol = "my_app_boot"
```

- **`owns_main = true`**: Omits Geisha's C `main()` wrapper so the native host (e.g., Cocoa/UIKit) owns the entry point and calls `boot_symbol` + exported Geisha functions.
- **`exports`**: Preserves the listed Geisha symbols with C ABI visibility.

### Conditional Native Rules (`[[target.native.when]]`)

Use `[[target.native.when]]` for OS-, tool-, or `pkg-config`-conditional compilation:

```toml
[[target.native.when]]
os         = "linux"
pkg_config = "sdl2"
defines    = ["HAVE_SDL2=1"]

[[target.native.when]]
tool       = "nvcc"
compiler   = "nvcc"
c_sources  = ["native/kernel.cu"]
c_flags    = ["-O3"]
link_flags = ["-lcudart"]
defines    = ["USE_CUDA=1"]
```

Predicates:
- `os`: Matches host OS string.
- `tool`: Checks `command -v <tool>` (can be disabled in CI/testing via `GEISHA_DISABLE_TOOL=<tool>`).
- `pkg_config`: Checks `pkg-config --exists <name>` and automatically appends `--cflags` / `--libs`.

---

## 3. WebAssembly (`[target.wasm32]`)

```toml
[target.wasm32]
exports    = ["app_init", "app_step"]
web_assets = ["host/web/index.html", "host/web/runtime.js"]
```

Build with:
```sh
geisha build --target wasm32
```

Requires LLVM `clang` with `wasm32` target support and `wasm-ld` (`lld`), plus `wasm_rt.o` (built via `make wasm-runtime`).

---

## 4. iOS & iOS Simulator (`ios` / `ios-sim`)

Build static runtime archives once in `geisha.gsa`:
```sh
make runtime-ios runtime-ios-sim
make install
```

Then compile your Geisha library/app as a static archive (`.a`) with `--no-main` and `--export` for linking into an Xcode target:

```sh
geisha build --target ios --no-main --export app_init --export app_step -o build/libapp_ios.a
geisha build --target ios-sim --no-main --export app_init --export app_step -o build/libapp_iossim.a
```

---

## 5. Module Layout & Package Scoping

- **Path-as-module**: `use my_lib.math.vec2.{Vec2, dot}` loads `src/math/vec2.gsa` (or from `my_lib`'s `src_dir`).
- **Hermeticity**: A package only sees dependencies declared in its own `geisha.toml` `[deps]`.
- **Orphan Rule**: Library packages may only define `instance Concept Type` if the package owns `Concept` or `Type`.
