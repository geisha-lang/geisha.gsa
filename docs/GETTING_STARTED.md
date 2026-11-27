# Getting Started with Geisha

This guide walks you through installing the Geisha toolchain, running scripts, creating packages, and using Geisha's type system, concurrency, and cross-compilation features.

---

## 1. Installation

Build and install the self-hosted compiler (`geisha`), native runtime (`libgeisha_runtime.a`), and WebAssembly runtime (`wasm_rt.o`) into `~/.geisha`:

```sh
make runtime wasm-runtime bootstrap
make install
```

Ensure `~/.geisha/bin` (or `~/.local/bin`) is on your `PATH`, then verify:

```sh
geisha --help
geisha guide
```

---

## 2. Quickstart: Scripts & Inline Evaluation

Geisha supports standalone script mode—no `geisha.toml` or `def main()` required:

```sh
# Evaluate an inline snippet
geisha eval 'printLn("Hello from Geisha! 2 + 3 = " + std.str.intToStr(2 + 3))'
```

Or save a file `hello.gsa`:

```geisha
#!/usr/bin/env -S geisha run
use std.str.intToStr

let name = "Geisha";
let n = 7;
printLn("Hello, " + name + "! Answer = " + intToStr(n * 6))
```

Run it directly:

```sh
geisha run hello.gsa
```

Scripts are compiled once and cached by content hash under `~/.geisha/cache/scripts/`.

---

## 3. Creating a Project

```sh
geisha init my_app
cd my_app
geisha check      # Fast frontend type/exhaustiveness/Send check
geisha run        # Build & run
geisha test       # Run tests/*.gsa
```

For a library package:

```sh
geisha init --lib my_lib
```

---

## 4. Language Tour

### Functions, Control Flow & Mutable Cells

Bindings with `let` are immutable. For local mutable state, use `Cell a`:

```geisha
use std.str.intToStr

def sumTo(n: Int): Int = {
    let acc = cellNew(0);
    let i = cellNew(1);
    while (cellGet(i) <= n) {
        cellSet(acc, cellGet(acc) + cellGet(i));
        cellSet(i, cellGet(i) + 1)
    };
    cellGet(acc)
}

def main(): Void = {
    let s = sumTo(10);
    if (s == 55) {
        printLn("ok: " + intToStr(s))
    } else {
        printLn("unexpected")
    }
}
```

> **Note**: Parentheses around `if (...)` and `while (...)` conditions are required, `else` is always required, and the final item in a `{ ... }` block has no trailing `;`.

### Algebraic Data Types, Records & Exhaustive Matching

```geisha
pub data Shape {
    Circle(Float),
    Rect { w: Float, h: Float },
}

def area(s: Shape): Float = match s {
    Circle(r) -> 3.141592653589793 * r * r,
    Rect { w, h } -> w * h,
}
```

Missing a variant in `match` is a compile-time error.

### Concepts & Zero-Keyword Deriving

```geisha
pub data User : Eq {
    name: String,
    age: Int,
}
```

Use `geisha doc std.generic` or `geisha doc std.codec` to inspect derivable concepts.

### Error Handling with `Result` and `?`

```geisha
use std.result.{Result, Ok, Err}
use std.str.parseInt

def parsePair(a: String, b: String): Result Int String = {
    let x = parseInt(a)?;
    let y = parseInt(b)?;
    Ok(x + y)
}
```

### Safe Concurrency (`Task`, `Actor`, `parTabulate`)

- **Data parallelism**: `parTabulate(n, i -> i * i)` computes an `ImmArray Int` in parallel; the compiler statically verifies that the closure captures no `Cell`/`MutArray` (`$Shared`) and the result type is `Send`.
- **Actors**: `Actor s` encapsulates `!Send` mutable state `s` behind a sequential mailbox, while `Actor s` itself is `Send`.

### Zero-Copy Scoped FFI (`ForeignPtr` & `ScopedPtr`)

```geisha
def readHeader(): Int = {
    let fp = foreignPtrAlloc(intToI64(64));
    withForeignPtr(fp, p -> {
        scopedPtrSetByte(p, 0, 42);
        scopedPtrByteAt(p, 0)
    })
}
```

The compiler prevents `p: ScopedPtr` or a `$Scoped` closure from escaping `withForeignPtr`.

---

## 5. Exploring the Standard Library

Never guess APIs—query the compiler directly:

```sh
geisha doc              # List all std.*, sys.*, and project modules
geisha doc std.str      # Inspect public types and functions in std.str
geisha doc std.json     # Inspect JSON parser/serializer APIs
```

---

## 6. Next Steps

- Read the full [Language Specification](SPEC.md)
- Configure dependencies, C/ObjC interop, Wasm32 & iOS targets in [Packages & Targets](PACKAGES_AND_TARGETS.md)
- Explore the Lean 4 safety proofs in [`formal/SPEC.md`](../formal/SPEC.md)
