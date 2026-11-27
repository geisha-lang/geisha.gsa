#!/usr/bin/env python3
"""End-to-end tests for `geisha test --watch` and `geisha run --watch`."""

from __future__ import annotations

import os
import queue
import subprocess
import sys
import tempfile
import threading
import time
from pathlib import Path


class StreamReader:
    """Cross-platform (POSIX + Windows) non-blocking line reader for a subprocess pipe."""

    def __init__(self, stream) -> None:
        self._q: queue.Queue[str | None] = queue.Queue()
        self._buf: list[str] = []
        self._thread = threading.Thread(target=self._pump, args=(stream,), daemon=True)
        self._thread.start()

    def _pump(self, stream) -> None:
        try:
            for line in iter(stream.readline, ""):
                self._q.put(line)
        finally:
            self._q.put(None)

    def read_until(self, needle: str, timeout: float = 20.0) -> str:
        deadline = time.monotonic() + timeout
        collected: list[str] = []
        while time.monotonic() < deadline:
            remaining = max(0.05, deadline - time.monotonic())
            try:
                item = self._q.get(timeout=min(0.2, remaining))
            except queue.Empty:
                continue
            if item is None:
                break
            collected.append(item)
            joined = "".join(collected)
            if needle in joined:
                return joined
        joined = "".join(collected)
        raise AssertionError(f"Timed out waiting for {needle!r}; output so far:\n{joined}")


def atomic_write(path: Path, text: str) -> None:
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(text, encoding="utf-8")
    os.replace(tmp, path)


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
        reader = StreamReader(proc.stdout)
        try:
            out1 = reader.read_until("Watching for changes...")
            assert "WATCH_TEST_OK" in out1 and "All 1 test target(s) passed." in out1, f"unexpected initial test output:\n{out1}"

            # 1. Break the code -> watcher reports failure and keeps watching
            time.sleep(0.1)
            atomic_write(lib_path, "pub def answer(): Int = 99\n")
            out2 = reader.read_until("Watching for changes...")
            assert "Change detected" in out2 and "test suite failed" in out2, f"expected failure re-run:\n{out2}"

            # 2. Fix the code -> watcher re-runs and passes again
            time.sleep(0.1)
            atomic_write(lib_path, "pub def answer(): Int = 42\n")
            out3 = reader.read_until("Watching for changes...")
            assert "Change detected" in out3 and "All 1 test target(s) passed." in out3, f"expected passing re-run:\n{out3}"

            # 3. Edit geisha.toml -> watcher detects manifest change and re-runs
            time.sleep(0.1)
            atomic_write(toml_path, 'name = "watch_demo"\nversion = "0.1.1"\n')
            out4 = reader.read_until("Watching for changes...")
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
        reader = StreamReader(proc.stdout)
        try:
            out1 = reader.read_until("Watching for changes...")
            assert "RUN_V1" in out1, f"expected RUN_V1 in initial run:\n{out1}"

            time.sleep(0.1)
            atomic_write(script_path, "def main(): Void = printLn(\"RUN_V2\")\n")
            out2 = reader.read_until("Watching for changes...")
            assert "Change detected" in out2 and "RUN_V2" in out2, f"expected RUN_V2 after edit:\n{out2}"
        finally:
            stop_proc(proc)


def test_watch_run_long_running_and_sigterm(geisha_bin: str, env: dict[str, str]) -> None:
    """Verify `geisha run --watch` restarts a still-running child on edit and cleans up its process group on SIGTERM."""
    import re
    import signal

    def pid_alive(pid: int) -> bool:
        if sys.platform == "win32":
            import ctypes
            from ctypes import wintypes

            SYNCHRONIZE = 0x00100000
            WAIT_TIMEOUT = 0x00000102
            ERROR_INVALID_PARAMETER = 87
            kernel32 = ctypes.WinDLL("kernel32", use_last_error=True)
            kernel32.OpenProcess.argtypes = [wintypes.DWORD, wintypes.BOOL, wintypes.DWORD]
            kernel32.OpenProcess.restype = ctypes.c_void_p
            kernel32.WaitForSingleObject.argtypes = [ctypes.c_void_p, wintypes.DWORD]
            kernel32.WaitForSingleObject.restype = wintypes.DWORD
            kernel32.CloseHandle.argtypes = [ctypes.c_void_p]
            kernel32.CloseHandle.restype = wintypes.BOOL
            h = kernel32.OpenProcess(SYNCHRONIZE, False, pid)
            if not h:
                return ctypes.get_last_error() != ERROR_INVALID_PARAMETER
            try:
                return kernel32.WaitForSingleObject(h, 0) == WAIT_TIMEOUT
            finally:
                kernel32.CloseHandle(h)
        try:
            os.kill(pid, 0)
            return True
        except ProcessLookupError:
            return False
        except PermissionError:
            return True
        except OSError:
            return False

    with tempfile.TemporaryDirectory(prefix="geisha_watch_daemon_") as td:
        root = Path(td)
        script_path = root / "server.gsa"
        script_v1 = (
            "use std.task.sleepMs\n"
            "use std.str.intToStr\n"
            "extern \"gs_sys_getpid\" def c_getpid(): Int\n"
            "def main(): Void = {\n"
            "    printLn(\"SERVER_V1_PID=\" + intToStr(c_getpid()));\n"
            "    while (true) { sleepMs(50) }\n"
            "}\n"
        )
        script_v2 = (
            "use std.task.sleepMs\n"
            "use std.str.intToStr\n"
            "extern \"gs_sys_getpid\" def c_getpid(): Int\n"
            "def main(): Void = {\n"
            "    printLn(\"SERVER_V2_PID=\" + intToStr(c_getpid()));\n"
            "    while (true) { sleepMs(50) }\n"
            "}\n"
        )
        script_path.write_text(script_v1, encoding="utf-8")

        proc = subprocess.Popen(
            [geisha_bin, "run", "--watch", str(script_path)],
            cwd=str(root),
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            env=env,
        )
        reader = StreamReader(proc.stdout)
        pid1 = None
        pid2 = None
        try:
            out1 = reader.read_until("SERVER_V1_PID=")
            m1 = re.search(r"SERVER_V1_PID=(\d+)", out1)
            assert m1 is not None, f"missing PID in V1 output:\n{out1}"
            pid1 = int(m1.group(1))
            assert pid_alive(pid1), f"expected V1 child pid {pid1} to be running"

            # Edit while V1 child is STILL RUNNING -> watcher must kill V1 and start V2!
            time.sleep(0.1)
            atomic_write(script_path, script_v2)
            out2 = reader.read_until("SERVER_V2_PID=")
            m2 = re.search(r"SERVER_V2_PID=(\d+)", out2)
            assert m2 is not None, f"missing PID in V2 output:\n{out2}"
            pid2 = int(m2.group(1))
            assert pid2 != pid1, f"expected new PID on restart, got same {pid2}"
            # V1 child must be dead & reaped
            deadline = time.monotonic() + 3.0
            while pid_alive(pid1) and time.monotonic() < deadline:
                time.sleep(0.05)
            assert not pid_alive(pid1), f"V1 child pid {pid1} leaked after watch restart!"
            assert pid_alive(pid2), f"expected V2 child pid {pid2} to be running"

            # Send SIGTERM to watcher (POSIX) -> watcher exits cleanly and does NOT leave pid2 as an orphan!
            if os.name != "nt":
                proc.send_signal(signal.SIGTERM)
                rc = proc.wait(timeout=5)
                assert rc == 0, f"expected clean exit code 0 on SIGTERM, got {rc}"
                deadline2 = time.monotonic() + 3.0
                while pid_alive(pid2) and time.monotonic() < deadline2:
                    time.sleep(0.05)
                assert not pid_alive(pid2), f"V2 child pid {pid2} left orphaned after watcher SIGTERM!"
            else:
                proc.terminate()
                proc.wait(timeout=5)
        finally:
            stop_proc(proc)
            if os.name != "nt":
                for p in (pid1, pid2):
                    if p is not None and pid_alive(p):
                        try:
                            os.kill(p, signal.SIGKILL)
                        except ProcessLookupError:
                            pass


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
    test_watch_run_long_running_and_sigterm(geisha_bin, env)
    print("PASS [geisha_watch]: `geisha test --watch` (src + geisha.toml) and `geisha run --watch` (restart + SIGTERM cleanup) verified!")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
