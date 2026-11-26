# AGENTS.md — Compiler & Language Maintenance Rules (`geisha.gsa`)

This repository is the self-hosting Geisha compiler, standard library, and package manager.
Because Geisha is a custom language not present in LLM pretraining corpora, **keeping machine-readable documentation and compiler diagnostics in sync with the language is a mandatory invariant**, not an afterthought.

## Mandatory Sync Rules When Changing Language Features

Whenever you modify any language-facing surface:
- **Syntax / Lexer / Parser** (`src/lexer.gsa`, `src/parser.gsa`, `src/ast.gsa`)
- **Type System / Concepts / Deriving / Ownership / Concurrency** (`src/infer.gsa`, `src/core.gsa`, `src/loader.gsa`)
- **CLI / Package Manifest** (`src/geisha.gsa`, `src/pkg.gsa`)
- **Standard Library** (`stdlib/std/*.gsa`, `stdlib/sys/*.gsa`)

You **MUST** in the same commit / PR:
1. **Update `AGENT_GUIDE.md`**:
   - Reflect new/changed syntax, semantics, CLI subcommands, `geisha.toml` fields, or stdlib modules.
   - Add any new common pitfall to the **Top LLM Pitfalls** table if agents are likely to miswrite it.
2. **Keep `///` doc comments accurate** on public APIs in `stdlib/` (consumed directly by `geisha doc <module>`).
3. **Regenerate embedded bundles**:
   ```sh
   make stdlib-bundle
   ```
   This refreshes both `src/stdlib_bundle.gsa` (for `std.*`/`sys.*` + `geisha doc`) and `src/guide_bundle.gsa` (for `geisha guide`).
4. **Verify before finishing**:
   ```sh
   make check-docs
   make runtime wasm-runtime bootstrap
   make test
   ```

## Enforcement

- `scripts/check_agent_docs.py` runs in `make check-docs`, `make test`, and GitHub Actions CI:
  - Verifies `src/stdlib_bundle.gsa` and `src/guide_bundle.gsa` are fresh and match `stdlib/` and `AGENT_GUIDE.md`.
  - Verifies every `stdlib/{std,sys}/*.gsa` module is registered in `scripts/gen_stdlib.py` and indexed in `AGENT_GUIDE.md`.
  - Verifies every CLI subcommand in `src/geisha.gsa` (`isSubcommandWord`) is documented in `printUsage()` and `AGENT_GUIDE.md`.
  - On Pull Requests (`--diff`), requires `AGENT_GUIDE.md` to be updated whenever language-surface files change, unless the commit/PR message explicitly contains `[docs-exempt]` for pure internal refactors or bugfixes with no user-visible change.

## Compiler Diagnostics Convention

- Never introduce raw `at byte N` error messages in `lexer.gsa`, `parser.gsa`, or `infer.gsa`.
- Always route span-bearing errors through `diag.formatDiagAt` / `diag.formatSpanDiag` so errors include `file:line:col`, the source line, and a `^~~~` caret.
