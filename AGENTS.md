# AGENTS.md — Compiler & Language Maintenance Rules (`geisha.gsa`)

This repository is the self-hosting Geisha compiler, standard library, and package manager.
Because Geisha is a custom language not present in LLM pretraining corpora, **keeping machine-readable documentation and compiler diagnostics in sync with the language is a mandatory invariant**, not an afterthought.

## Branch, Worktree & Pull Request Workflow (No Direct Push to `main`)

`main` is protected on GitHub and gated by cross-platform CI (`linux-x86_64`, `linux-arm64`, `darwin-arm64`) and Lean 4 formal verification.

1. **Never edit or commit on `main` in the shared `~/code/geisha.gsa` checkout**:
   - Keep `~/code/geisha.gsa` strictly on clean `main` (used only to `git pull --ff-only` and `make runtime wasm-runtime bootstrap && make install` into `~/.geisha`).
   - Always create an isolated `git worktree` in your session workspace on a feature/fix branch (`git -C ~/code/geisha.gsa worktree add -b <type>/<topic> <workspace>/geisha-wt origin/main`).
2. **Open a Pull Request & wait for all 4 CI jobs before merging**:
   - Push your branch (`git push -u origin <branch>`), open a PR with `gh pr create`, and enable auto-merge (`gh pr merge --squash --auto --delete-branch`) or merge only after all 4 required checks succeed.
   - Never bypass branch protection or push directly to `main`.

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
- Always route span-bearing errors through `diag.formatDiagAt` / `diag.formatSpanDiag` / `diag.formatSpanDiagHint` so errors emit compact 1D `file:line:col: error[kind]: ...` + `near:` + `line N:` + optional `hint:` (no 2D ASCII-art caret padding).
