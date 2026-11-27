# Debugging Geisha Programs (DWARF, LLDB, GDB & VS Code CodeLLDB)

Geisha compiles to LLVM 20 IR and supports full source-level DWARF debug information via `-g` / `--debug`.

## 1. Building with Debug Info

```sh
# Single file
geisha -g -o app main.gsa

# geisha.toml project
geisha build -g

# Inspect generated LLVM 20 IR with DWARF metadata
geisha -g -e -o main.ll main.gsa

# Override optimization level (default is -O0 when -g is set, -O2 otherwise)
# Accepts -O0..-O3, -Os, -Oz, --opt[=]<0|1|2|3|s|z>, --dev (-O0), --release (-O2)
geisha -g -O2 -o app main.gsa
```

What `-g` / `--debug` does:
- Emits DWARF v4 metadata (`!DICompileUnit`, `!DIFile`, `!DISubprogram`, `!DILocation`, `@llvm.dbg.declare`, `!DILocalVariable`, and Geisha primitive / Tuple / ADT types).
- Defaults LLVM optimization to `-O0` (unless `-O1`/`-O2`/`-O3` is explicitly passed) and disables tail-call optimization so every stack frame and local variable remains inspectable.
- On **macOS**, compiles via an intermediate `.o` and runs `dsymutil <binary>` to generate `<binary>.dSYM` before cleaning up `.o`.
- On **Linux**, links DWARF sections directly into the ELF binary.
- Without `-g`, generated LLVM IR is completely unchanged.

## 2. Debugging with LLDB (macOS / Linux)

```sh
lldb ./app
```

Load the Geisha LLDB data formatters (installed to `~/.geisha/lib/geisha_lldb.py` by `make install`):

```lldb
(lldb) command script import ~/.geisha/lib/geisha_lldb.py
(lldb) b main.gsa:15
(lldb) run
(lldb) bt
(lldb) frame variable
```

`geisha_lldb.py` formats:
- `String` as `"..."`
- `Vec a` as `Vec(len=N) [e0, e1, ...]`
- `MutArray a` / `ImmArray a` as `Array(len=N) [e0, e1, ...]`
- `List a` as `[e0, e1, ...]`
- `Option a` as `None` / `Some(...)`
- Other boxed ADTs as `TypeName(tag=T, payload=...)`

(To auto-load on every LLDB session, add `command script import ~/.geisha/lib/geisha_lldb.py` to `~/.lldbinit`.)

## 3. Debugging with GDB (Linux)

```sh
gdb ./app
(gdb) break main.gsa:15
(gdb) run
(gdb) bt
(gdb) info locals
```

## 4. VS Code Integration (CodeLLDB)

Install the **CodeLLDB** extension (`vadimcn.vscode-lldb`) in VS Code — no custom DAP server is needed.

### `.vscode/tasks.json`

```json
{
  "version": "2.0.0",
  "tasks": [
    {
      "label": "geisha: build debug",
      "type": "shell",
      "command": "geisha build -g -o build/debug",
      "group": {
        "kind": "build",
        "isDefault": true
      },
      "problemMatcher": []
    }
  ]
}
```

### `.vscode/launch.json`

```json
{
  "version": "0.2.0",
  "configurations": [
    {
      "name": "Debug Geisha (CodeLLDB)",
      "type": "lldb",
      "request": "launch",
      "preLaunchTask": "geisha: build debug",
      "program": "${workspaceFolder}/build/debug",
      "args": [],
      "cwd": "${workspaceFolder}",
      "initCommands": [
        "command script import ~/.geisha/lib/geisha_lldb.py"
      ]
    }
  ]
}
```

Set breakpoints directly in `.gsa` files and press **F5** to build, launch, step, inspect call stacks, and view Geisha variables in the VS Code Variables pane.
