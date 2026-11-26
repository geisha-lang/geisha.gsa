#!/usr/bin/env python3
"""Guardrail script enforcing that Geisha's agent docs, bundles, and diagnostics stay in sync."""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))
import gen_stdlib  # noqa: E402

LANGUAGE_SURFACE_FILES = {
    "src/ast.gsa",
    "src/lexer.gsa",
    "src/parser.gsa",
    "src/infer.gsa",
    "src/core.gsa",
    "src/loader.gsa",
    "src/pkg.gsa",
    "src/geisha.gsa",
}


def check_bundles(errors: list[str]) -> None:
    expected_stdlib = gen_stdlib.render_stdlib_bundle()
    actual_stdlib = gen_stdlib.STDLIB_OUT.read_text(encoding="utf-8") if gen_stdlib.STDLIB_OUT.exists() else ""
    if actual_stdlib != expected_stdlib:
        errors.append(
            "src/stdlib_bundle.gsa is out of sync with stdlib/ or scripts/gen_stdlib.py — run `make stdlib-bundle`."
        )

    if not gen_stdlib.GUIDE_MD.exists():
        errors.append("AGENT_GUIDE.md is missing.")
        return

    expected_guide = gen_stdlib.render_guide_bundle()
    actual_guide = gen_stdlib.GUIDE_OUT.read_text(encoding="utf-8") if gen_stdlib.GUIDE_OUT.exists() else ""
    if actual_guide != expected_guide:
        errors.append(
            "src/guide_bundle.gsa is out of sync with AGENT_GUIDE.md — run `make stdlib-bundle`."
        )


def check_stdlib_coverage(errors: list[str]) -> None:
    guide_text = gen_stdlib.GUIDE_MD.read_text(encoding="utf-8")
    registered = {rel for _, rel in gen_stdlib.MODULES}
    on_disk = {
        p.relative_to(gen_stdlib.STDLIB_DIR).as_posix()
        for p in sorted(gen_stdlib.STDLIB_DIR.glob("*/*.gsa"))
    }
    missing_from_gen = sorted(on_disk - registered)
    if missing_from_gen:
        errors.append(
            f"stdlib files not registered in scripts/gen_stdlib.py: {', '.join(missing_from_gen)}"
        )

    missing_from_guide = [
        mod_key for mod_key, _ in gen_stdlib.MODULES if f"`{mod_key}`" not in guide_text
    ]
    if missing_from_guide:
        errors.append(
            f"stdlib modules missing from AGENT_GUIDE.md index: {', '.join(missing_from_guide)}"
        )


def check_cli_coverage(errors: list[str]) -> None:
    driver_src = (ROOT / "src" / "geisha.gsa").read_text(encoding="utf-8")
    guide_text = gen_stdlib.GUIDE_MD.read_text(encoding="utf-8")

    m = re.search(r"def isSubcommandWord\b.*?\n\n", driver_src, flags=re.S)
    if not m:
        errors.append("Could not locate `isSubcommandWord` in src/geisha.gsa.")
        return
    subcmds = re.findall(r'w == "([a-z0-9_-]+)"', m.group(0))

    usage_m = re.search(r"def printUsage\b.*?\n\}\n", driver_src, flags=re.S)
    usage_text = usage_m.group(0) if usage_m else ""

    for sc in subcmds:
        if f"geisha {sc}" not in usage_text:
            errors.append(f"CLI subcommand `geisha {sc}` is not documented in printUsage() (src/geisha.gsa).")
        if f"geisha {sc}" not in guide_text:
            errors.append(f"CLI subcommand `geisha {sc}` is not documented in AGENT_GUIDE.md.")


def check_no_raw_byte_errors(errors: list[str]) -> None:
    for rel in ("src/lexer.gsa", "src/parser.gsa", "src/infer.gsa"):
        text = (ROOT / rel).read_text(encoding="utf-8")
        for lineno, line in enumerate(text.splitlines(), 1):
            if "at byte " in line and not line.lstrip().startswith("//"):
                errors.append(
                    f"{rel}:{lineno}: raw `at byte` error found; use diag.formatDiagAt / diag.formatSpanDiag instead."
                )


def check_diff_guard(diff_range: str, errors: list[str]) -> None:
    res = subprocess.run(
        ["git", "diff", "--name-only", diff_range],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=True,
    )
    changed = [line.strip() for line in res.stdout.splitlines() if line.strip()]
    touched_lang = [
        f for f in changed if f in LANGUAGE_SURFACE_FILES or f.startswith("stdlib/")
    ]
    if not touched_lang or "AGENT_GUIDE.md" in changed:
        return

    log_res = subprocess.run(
        ["git", "log", "--format=%B", diff_range],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=True,
    )
    if "[docs-exempt]" in log_res.stdout:
        return

    errors.append(
        "Language/stdlib surface files changed ("
        + ", ".join(touched_lang)
        + ") without updating AGENT_GUIDE.md. Update AGENT_GUIDE.md + run `make stdlib-bundle`, "
        "or include `[docs-exempt]` in the commit message for pure internal fixes."
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--diff",
        default=None,
        help="Optional git revision range (e.g. origin/main..HEAD) to enforce AGENT_GUIDE.md updates on language changes.",
    )
    args = parser.parse_args()

    errors: list[str] = []
    check_bundles(errors)
    check_stdlib_coverage(errors)
    check_cli_coverage(errors)
    check_no_raw_byte_errors(errors)
    if args.diff:
        check_diff_guard(args.diff, errors)

    if errors:
        print("Agent docs / compiler sync check FAILED:", file=sys.stderr)
        for e in errors:
            print(f"  - {e}", file=sys.stderr)
        return 1

    print("Agent docs & bundle sync check OK.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
