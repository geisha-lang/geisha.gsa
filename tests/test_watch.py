#!/usr/bin/env python3
"""End-to-end tests for `geisha test --watch` and `geisha run --watch`."""

from __future__ import annotations

import os
import select
import subprocess
import sys
import tempfile
import time
from pathlib import Path


def read_until(proc: subprocess.Popen[str], needle: str, timeout: float = 20.0) -> str:
    """Read combined stdout+stderr from `proc` until `needle` appears or timeout expires."""
    assert proc.stdout is not None
    fd = proc.stdout.fileno()
    buf = []
    deadline = time.monotonic() + timeout
    while time.monotonic() < deadline:
        remaining = max(0.05, deadline - time.monotonic())
        ready, _, _ = select.select([fd], [], [], min(0.2, remaining))
        if ready:
            chunk = os.read(fd, 4096).decode("utf-8", errors="replace")
            if not chunk:
                break
            buf.append(chunk)
            joined = "".join(buf)
            if needle in joined:
                return joined
        elif proc.poll() is not None:
            break
    joined = "".join(buf)
    raise AssertionError(f"Timed out waiting for {needle!r}; output so far:\n{joined}")


def stop_proc(proc: subprocess.Popen[str]) -> None:
    if proc.poll() is None:
        proc.terminate()
        try:
            proc.wait(timeout=5)
        except subprocess.TimeoutExpired:
            proc.kill()
            proc.wait(timeout=5)


def test_watch_test_project(geisha_bin: str, env: dict[str, str]) -> None:
    with tempfile.TemporaryDirectory(prefix="geisha_watch_test_") as td:
        root = Path(td)
        (root / "src").mkdir()
        (root / "tests").mkdir()
        toml_path = root / "geisha.toml"
        toml_path.write_text('name = "watch_demo"\nversion = "0.1.0"\n', encoding="utf-8")
        lib_path = root / "src" / "watch_demo.gsa"
        lib_path.write_text("pub def answer(): Int = 42\n", encoding="utf-8")
        spec_path = root / "tests" / "spec.gsa"
        spec_path.write_text(
            "use watch_demo.answer\n"
            "use sys.proc.exit\n"
            "def main(): Void = if (answer() == 42) printLn(\"WATCH_TEST_OK\") else exit(1)\n",
            encoding="utf-8",
        )

        proc = subprocess.Popen(
            [geisha_bin, "test", "--watch"],
            cwd=str(root),
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            env=env,
        )
        try:
            out1 = read_until(proc, "Watching for changes...")
            assert "WATCH_TEST_OK" in out1 and "All 1 test target(s) passed." in out1, f"unexpected initial test output:\n{out1}"

            # 1. Break the code -> watcher reports failure and keeps watching
            time.sleep(0.1)
            lib_path.write_text("pub def answer(): Int = 99\n", encoding="utf-8")
            out2 = read_until(proc, "Watching for changes...")
            assert "Change detected" in out2 and "test suite failed" in out2, f"expected failure re-run:\n{out2}"

            # 2. Fix the code -> watcher re-runs and passes again
            time.sleep(0.1)
            lib_path.write_text("pub def answer(): Int = 42\n", encoding="utf-8")
            out3 = read_until(proc, "Watching for changes...")
            assert "Change detected" in out3 and "All 1 test target(s) passed." in out3, f"expected passing re-run:\n{out3}"

            # 3. Edit geisha.toml -> watcher detects manifest change and re-runs
            time.sleep(0.1)
            toml_path.write_text('name = "watch_demo"\nversion = "0.1.1"\n', encoding="utf-8")
            out4 = read_until(proc, "Watching for changes...")
            assert "Change detected" in out4 and "All 1 test target(s) passed." in out4, f"expected geisha.toml re-run:\n{out4}"
        finally:
            stop_proc(proc)


def test_watch_run_script(geisha_bin: str, env: dict[str, str]) -> None:
    with tempfile.TemporaryDirectory(prefix="geisha_watch_run_") as td:
        root = Path(td)
        script_path = root / "hello.gsa"
        script_path.write_text("def main(): Void = printLn(\"RUN_V1\")\n", encoding="utf-8")

        proc = subprocess.Popen(
            [geisha_bin, "run", "--watch", str(script_path)],
            cwd=str(root),
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            env=env,
        )
        try:
            out1 = read_until(proc, "Watching for changes...")
            assert "RUN_V1" in out1, f"expected RUN_V1 in initial run:\n{out1}"

            time.sleep(0.1)
            script_path.write_text("def main(): Void = printLn(\"RUN_V2\")\n", encoding="utf-8")
            out2 = read_until(proc, "Watching for changes...")
            assert "Change detected" in out2 and "RUN_V2" in out2, f"expected RUN_V2 after edit:\n{out2}"
        finally:
            stop_proc(proc)


def main() -> int:
    geisha_bin = sys.argv[1] if len(sys.argv) > 1 else os.environ.get("GEISHA_BIN", "build/geisha2")
    geisha_bin = str(Path(geisha_bin).resolve())
    env = os.environ.copy()
    if env.get("GEISHA_RUNTIME"):
        env["GEISHA_RUNTIME"] = str(Path(env["GEISHA_RUNTIME"]).resolve())
    env["GEISHA_WATCH_POLL_MS"] = "50"
    env["GEISHA_WATCH_NO_CLEAR"] = "1"

    test_watch_test_project(geisha_bin, env)
    test_watch_run_script(geisha_bin, env)
    print("PASS [geisha_watch]: `geisha test --watch` (src + geisha.toml) and `geisha run --watch` verified!")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
