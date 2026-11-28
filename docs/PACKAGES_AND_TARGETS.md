# Packages, Targets & FFI Interop

This document covers Geisha's decentralized Git/MVS package manager (`geisha.toml`), local overrides (`geisha.local.toml`), conditional native builds, and cross-compilation to `wasm32`, `js` (ES Module + `.d.ts`), `ios`, and `ios-sim`.

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

# Optional machine-local target & code-signing overrides (keeps geisha.toml CI-portable):
[target.macos]
codesign = "Apple Development"
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

## 3. WebAssembly (`[target.wasm32]`) & Size Optimization

```toml
[target.wasm32]
exports      = ["app_init", "app_step"]
web_assets   = ["host/web/index.html", "host/web/runtime.js"]
opt          = "z"        # "0" | "1" | "2" (default) | "3" | "s" | "z"
strip        = true       # defaults to true under opt = "s"/"z"; set false to retain name section
slim_runtime = false      # true omits default gs_wasm_* bridge exports so --gc-sections drops unused GC
```

Build with:
```sh
geisha build --target wasm32
geisha build --target wasm32 --opt z --strip --slim-runtime
```

Requires LLVM `clang` with `wasm32` target support and `wasm-ld` (`lld`), plus `wasm_rt.o` (built via `make wasm-runtime`). When `opt` is `"s"` or `"z"`, `geisha` automatically runs `wasm-opt -Oz` if available on `PATH` (set `GEISHA_DISABLE_TOOL=wasm-opt` to skip).

---

## 4. JavaScript / TypeScript (`[target.js]`) & Zero-Server Playground

```toml
[target.js]
exports    = ["add", "parseDoc"]   # defaults to root module `pub def`s when omitted
web_assets = ["host/web/index.html"]
dts        = true                  # emit companion `.d.ts` TypeScript declarations (default: true)
owns_main  = false                 # true skips auto-invoking `main()` on module import
```

Build directly or as a project:
```sh
geisha --target js -o app.mjs app.gsa      # emits app.mjs + app.d.ts
geisha build --target js                   # emits build/<name>.mjs + build/<name>.d.ts
```

---

## 5. iOS, macOS `.app` & `.appex` Bundles (`ios`, `ios-sim`, `macos-app`, `ios-app`, `ios-sim-app`)

Build static runtime archives once in `geisha.gsa`:
```sh
make runtime-ios runtime-ios-sim
make install
```

### Static Libraries (for Xcode / Swift embedding)
```sh
geisha build --target ios --no-main --export app_init --export app_step -o build/libapp_ios.a
geisha build --target ios-sim --no-main --export app_init --export app_step -o build/libapp_iossim.a
```

### Native Apple App & App Extension Bundles (Pure Geisha, No Xcode Project Needed)
Configure `[target.macos]` and/or `[target.ios]` in `geisha.toml`:

```toml
[target.macos]
bundle_id    = "com.example.myapp"
bundle_name  = "MyApp"
min_os       = "14.0"
frameworks   = ["Cocoa", "QuartzCore", "ScreenCaptureKit"]
lsui_element = true
icon         = "Resources/AppIcon.icns"
resources    = ["Resources/Dicts"]
entitlements = "Resources/app.entitlements"
codesign     = "-"

[target.ios]
bundle_id            = "com.example.myapp"
bundle_name          = "MyApp"
min_os               = "16.0"
frameworks           = ["UIKit", "Foundation", "QuartzCore"]
is_extension         = false         # set true for `.appex` (`-fapplication-extension -e _NSExtensionMain`)
extension_point      = "com.apple.keyboard-service"
principal_class      = "MyController"
provisioning_profile = "iOS/embedded.mobileprovision"
embed_extensions     = ["../my_keyboard/build/MyKeyboard.appex"]
codesign             = "-"
```

Build and run directly from the CLI:
```sh
geisha build --target macos-app
geisha run --target macos-app
geisha build --target ios-sim-app
geisha run --target ios-sim-app
geisha build --target ios-app
```

---

## 5. Module Layout & Package Scoping

- **Path-as-module**: `use my_lib.math.vec2.{Vec2, dot}` loads `src/math/vec2.gsa` (or from `my_lib`'s `src_dir`).
- **Hermeticity**: A package only sees dependencies declared in its own `geisha.toml` `[deps]`.
- **Orphan Rule**: Library packages may only define `instance Concept Type` if the package owns `Concept` or `Type`.
