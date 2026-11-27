#!/usr/bin/env python3
"""End-to-end JSON-RPC 2.0 stdio test suite for `geisha lsp`."""

from __future__ import annotations

import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path


class LspClient:
    def __init__(self, geisha_bin: str, cwd: str, extra_args: list[str] | None = None) -> None:
        cmd = [geisha_bin, "lsp"] + (extra_args or [])
        self.proc = subprocess.Popen(
            cmd,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            cwd=cwd,
        )
        self.next_id = 1
        self.notifications: list[dict] = []

    def send(self, payload: dict) -> None:
        body = json.dumps(payload).encode("utf-8")
        header = f"Content-Length: {len(body)}\r\n\r\n".encode("ascii")
        assert self.proc.stdin is not None
        self.proc.stdin.write(header + body)
        self.proc.stdin.flush()

    def read_message(self) -> dict:
        assert self.proc.stdout is not None
        content_len = None
        while True:
            line = self.proc.stdout.readline()
            if not line:
                stderr_out = self.proc.stderr.read().decode("utf-8", errors="replace") if self.proc.stderr else ""
                raise RuntimeError(f"Unexpected EOF from geisha lsp (stderr={stderr_out!r})")
            decoded = line.decode("ascii").strip()
            if decoded == "":
                if content_len is not None:
                    break
                continue
            if ":" in decoded:
                k, v = decoded.split(":", 1)
                if k.strip().lower() == "content-length":
                    content_len = int(v.strip())
        assert content_len is not None
        body = self.proc.stdout.read(content_len)
        return json.loads(body.decode("utf-8"))

    def request(self, method: str, params: dict | None = None) -> dict:
        req_id = self.next_id
        self.next_id += 1
        msg: dict = {"jsonrpc": "2.0", "id": req_id, "method": method}
        if params is not None:
            msg["params"] = params
        self.send(msg)
        while True:
            resp = self.read_message()
            if "id" in resp and resp["id"] == req_id:
                return resp
            self.notifications.append(resp)

    def notify(self, method: str, params: dict | None = None) -> None:
        msg: dict = {"jsonrpc": "2.0", "method": method}
        if params is not None:
            msg["params"] = params
        self.send(msg)

    def wait_notification(self, method: str) -> dict:
        for i, n in enumerate(self.notifications):
            if n.get("method") == method:
                return self.notifications.pop(i)
        while True:
            msg = self.read_message()
            if msg.get("method") == method:
                return msg
            self.notifications.append(msg)

    def wait_diag_for(self, uri: str) -> list[dict]:
        # Drain matching diagnostic notification for `uri`
        for i, n in enumerate(self.notifications):
            if n.get("method") == "textDocument/publishDiagnostics" and n.get("params", {}).get("uri") == uri:
                self.notifications.pop(i)
                return n["params"]["diagnostics"]
        while True:
            msg = self.read_message()
            if msg.get("method") == "textDocument/publishDiagnostics" and msg.get("params", {}).get("uri") == uri:
                return msg["params"]["diagnostics"]
            self.notifications.append(msg)


def path_to_uri(p: Path) -> str:
    return p.resolve().as_uri()


def main() -> int:
    geisha_bin = sys.argv[1] if len(sys.argv) > 1 else os.environ.get("GEISHA_BIN", "build/geisha2")
    geisha_bin = str(Path(geisha_bin).resolve())

    # 0. CLI argument validation: reject unknown flags & positional args immediately (no hang), accept --stdio
    bad_flag = subprocess.run([geisha_bin, "lsp", "--bogus"], stdin=subprocess.DEVNULL, capture_output=True, text=True, timeout=5)
    assert bad_flag.returncode != 0 and "--bogus" in bad_flag.stderr, f"expected error on --bogus: {bad_flag}"
    bad_pos = subprocess.run([geisha_bin, "lsp", "extra.gsa"], stdin=subprocess.DEVNULL, capture_output=True, text=True, timeout=5)
    assert bad_pos.returncode != 0 and "extra.gsa" in bad_pos.stderr, f"expected error on positional arg: {bad_pos}"

    with tempfile.TemporaryDirectory(prefix="geisha_lsp_test_") as td:
        root = Path(td)
        helper_path = root / "helper.gsa"
        helper_src = (
            "/// A boxed integer wrapper.\n"
            "pub data Boxed {\n"
            "    Wrap(Int),\n"
            "    Empty,\n"
            "}\n"
            "\n"
            "/// Multiply an integer by two.\n"
            "pub def doubleVal(n: Int): Int = n * 2\n"
        )
        helper_path.write_text(helper_src, encoding="utf-8")

        main_path = root / "main.gsa"
        main_src = (
            "use std.str.{intToStr}\n"
            "use helper.{Boxed, Wrap, Empty, doubleVal}\n"
            "\n"
            "/// A 2D integer point.\n"
            "pub data Point { x: Int, y: Int }\n"
            "\n"
            "pub data Shape {\n"
            "    Circle(Int),\n"
            "    Rect { w: Int, h: Int },\n"
            "}\n"
            "\n"
            "pub concept Describable a {\n"
            "    describe: a -> String\n"
            "}\n"
            "\n"
            "/// Add two integers together.\n"
            "def addNums(a: Int, b: Int): Int = a + b\n"
            "\n"
            "def unwrapBox(bx: Boxed): Int = match bx {\n"
            "    Wrap(val) -> val + 1,\n"
            "    Empty -> 0,\n"
            "}\n"
            "\n"
            "def main(): Void = {\n"
            "    let (px, py) = (10, 20);\n"
            "    let total = addNums(px, doubleVal(py)) + unwrapBox(Wrap(5));\n"
            "    printLn(intToStr(total))\n"
            "}\n"
        )
        main_path.write_text(main_src, encoding="utf-8")

        main_uri = path_to_uri(main_path)
        helper_uri = path_to_uri(helper_path)

        client = LspClient(geisha_bin, str(root), extra_args=["--stdio"])

        # 1. initialize + initialized
        init_resp = client.request("initialize", {
            "processId": os.getpid(),
            "rootUri": path_to_uri(root),
            "capabilities": {},
        })
        assert "result" in init_resp, f"initialize failed: {init_resp}"
        caps = init_resp["result"]["capabilities"]
        assert caps["hoverProvider"] is True
        assert caps["definitionProvider"] is True
        assert caps["referencesProvider"] is True
        assert caps["renameProvider"]["prepareProvider"] is True
        assert caps["inlayHintProvider"] is True
        assert "quickfix" in caps["codeActionProvider"]["codeActionKinds"]
        assert caps["documentSymbolProvider"] is True
        assert caps["completionProvider"]["triggerCharacters"] == ["."]
        assert init_resp["result"]["serverInfo"]["name"] == "geisha-lsp"
        client.notify("initialized", {})

        # 2. didOpen valid file -> 0 diagnostics
        client.notify("textDocument/didOpen", {
            "textDocument": {
                "uri": main_uri,
                "languageId": "geisha",
                "version": 1,
                "text": main_src,
            }
        })
        diag_ok = client.wait_notification("textDocument/publishDiagnostics")
        assert diag_ok["params"]["uri"] == main_uri
        assert diag_ok["params"]["diagnostics"] == [], f"expected 0 diagnostics, got: {diag_ok}"

        # 3. documentSymbol (and word-boundary selectionRange)
        sym_resp = client.request("textDocument/documentSymbol", {
            "textDocument": {"uri": main_uri},
        })
        syms = sym_resp["result"]
        sym_names = [s["name"] for s in syms]
        for expected in ("Point", "Shape", "Describable", "addNums", "unwrapBox", "main"):
            assert expected in sym_names, f"missing symbol {expected!r} in {sym_names}"
        shape_sym = next(s for s in syms if s["name"] == "Shape")
        variant_names = [c["name"] for c in shape_sym.get("children", [])]
        assert "Circle" in variant_names and "Rect" in variant_names, f"missing Shape variants: {variant_names}"
        desc_sym = next(s for s in syms if s["name"] == "Describable")
        method_names = [c["name"] for c in desc_sym.get("children", [])]
        assert "describe" in method_names, f"missing concept method: {method_names}"
        add_sym = next(s for s in syms if s["name"] == "addNums")
        assert add_sym["selectionRange"]["start"] == {"line": 16, "character": 4}, f"unexpected selectionRange: {add_sym}"

        # 4. hover on `addNums` call (line 25, col 18) -> inferred type + `///` doc
        hover_add = client.request("textDocument/hover", {
            "textDocument": {"uri": main_uri},
            "position": {"line": 25, "character": 18},
        })
        assert hover_add["result"] is not None, "hover on addNums returned null"
        hover_add_md = hover_add["result"]["contents"]["value"]
        assert "Int" in hover_add_md and "Add two integers together." in hover_add_md, f"unexpected hover: {hover_add_md}"

        # 4b. hover on `doubleVal` call (line 25, col 31) -> cross-file inferred type + `///` doc
        hover_dbl = client.request("textDocument/hover", {
            "textDocument": {"uri": main_uri},
            "position": {"line": 25, "character": 31},
        })
        assert hover_dbl["result"] is not None, "hover on doubleVal returned null"
        hover_dbl_md = hover_dbl["result"]["contents"]["value"]
        assert "Int" in hover_dbl_md and "Multiply an integer by two." in hover_dbl_md, f"unexpected hover: {hover_dbl_md}"

        # 4c. hover on `total` in `intToStr(total)` (line 26, col 22) -> inferred `Int`
        hover_tot = client.request("textDocument/hover", {
            "textDocument": {"uri": main_uri},
            "position": {"line": 26, "character": 22},
        })
        assert hover_tot["result"] is not None, "hover on total returned null"
        assert "Int" in hover_tot["result"]["contents"]["value"], f"unexpected hover on total: {hover_tot}"

        # 5. definition: top-level, cross-file fn, local param, local let, match pattern var, destructured let, cross-file pattern ctor
        def_add = client.request("textDocument/definition", {
            "textDocument": {"uri": main_uri},
            "position": {"line": 25, "character": 18},
        })
        assert def_add["result"]["uri"] == main_uri
        assert def_add["result"]["range"]["start"]["line"] == 16, f"unexpected addNums def: {def_add}"

        def_dbl = client.request("textDocument/definition", {
            "textDocument": {"uri": main_uri},
            "position": {"line": 25, "character": 31},
        })
        assert def_dbl["result"]["uri"] == helper_uri
        assert def_dbl["result"]["range"]["start"]["line"] == 7, f"unexpected doubleVal def: {def_dbl}"

        # Local param `a` in `def addNums(a: Int, b: Int): Int = a + b` (line 16, col 35 -> col 12)
        def_param = client.request("textDocument/definition", {
            "textDocument": {"uri": main_uri},
            "position": {"line": 16, "character": 35},
        })
        assert def_param["result"]["uri"] == main_uri
        assert def_param["result"]["range"]["start"] == {"line": 16, "character": 12}, f"unexpected param def: {def_param}"

        # Local `let total` usage on line 26, col 22 -> line 25, col 8
        def_let = client.request("textDocument/definition", {
            "textDocument": {"uri": main_uri},
            "position": {"line": 26, "character": 22},
        })
        assert def_let["result"]["uri"] == main_uri
        assert def_let["result"]["range"]["start"] == {"line": 25, "character": 8}, f"unexpected let def: {def_let}"

        # Match pattern binder `val` usage on line 19, col 18 -> line 19, col 9
        def_patvar = client.request("textDocument/definition", {
            "textDocument": {"uri": main_uri},
            "position": {"line": 19, "character": 18},
        })
        assert def_patvar["result"]["uri"] == main_uri
        assert def_patvar["result"]["range"]["start"] == {"line": 19, "character": 9}, f"unexpected patvar def: {def_patvar}"

        # Destructured `let (px, py)` usage `px` on line 25, col 25 -> line 24, col 9
        def_destr = client.request("textDocument/definition", {
            "textDocument": {"uri": main_uri},
            "position": {"line": 25, "character": 25},
        })
        assert def_destr["result"]["uri"] == main_uri
        assert def_destr["result"]["range"]["start"] == {"line": 24, "character": 9}, f"unexpected destructured let def: {def_destr}"

        # Cross-module pattern constructor `Wrap` on line 19, col 5 -> helper.gsa line 1
        def_ctor = client.request("textDocument/definition", {
            "textDocument": {"uri": main_uri},
            "position": {"line": 19, "character": 5},
        })
        assert def_ctor["result"] is not None, "cross-module pattern ctor definition returned null"
        assert def_ctor["result"]["uri"] == helper_uri, f"expected {helper_uri}, got {def_ctor}"
        assert def_ctor["result"]["range"]["start"]["line"] == 1, f"unexpected Boxed/Wrap def: {def_ctor}"

        # 6. completion: `std.`, `sys.`, `std.str.`, local defs, and preludePrimSpecs (`MutArray`, `immArrayGet`, no `__conc*`)
        comp_src = main_src + "\ndef _c1() = std.\ndef _c2() = sys.\ndef _c3() = std.str.\ndef _c4() = add\ndef _c5() = arrayN\ndef _c6() = immArray\n"
        client.notify("textDocument/didChange", {
            "textDocument": {"uri": main_uri, "version": 2},
            "contentChanges": [{"text": comp_src}],
        })
        _ = client.wait_notification("textDocument/publishDiagnostics")

        comp_std = client.request("textDocument/completion", {
            "textDocument": {"uri": main_uri},
            "position": {"line": 29, "character": 16},
        })
        std_labels = {it["label"] for it in comp_std["result"]["items"]}
        assert {"str", "json", "list", "vec", "map", "option", "result"}.issubset(std_labels)

        comp_sys = client.request("textDocument/completion", {
            "textDocument": {"uri": main_uri},
            "position": {"line": 30, "character": 16},
        })
        sys_labels = {it["label"] for it in comp_sys["result"]["items"]}
        assert {"io", "fs", "env", "proc"}.issubset(sys_labels)

        comp_str = client.request("textDocument/completion", {
            "textDocument": {"uri": main_uri},
            "position": {"line": 31, "character": 20},
        })
        str_labels = {it["label"] for it in comp_str["result"]["items"]}
        assert {"intToStr", "strStartsWith", "strJoin"}.issubset(str_labels)

        comp_local = client.request("textDocument/completion", {
            "textDocument": {"uri": main_uri},
            "position": {"line": 32, "character": 15},
        })
        local_labels = {it["label"] for it in comp_local["result"]["items"]}
        assert "addNums" in local_labels

        comp_arr = client.request("textDocument/completion", {
            "textDocument": {"uri": main_uri},
            "position": {"line": 33, "character": 18},
        })
        arr_item = next(it for it in comp_arr["result"]["items"] if it["label"] == "arrayNew")
        assert "MutArray" in arr_item["detail"], f"expected MutArray in arrayNew detail, got: {arr_item}"

        comp_imm = client.request("textDocument/completion", {
            "textDocument": {"uri": main_uri},
            "position": {"line": 34, "character": 20},
        })
        imm_labels = {it["label"] for it in comp_imm["result"]["items"]}
        assert "immArrayGet" in imm_labels and not any(l.startswith("__") for l in imm_labels)

        # 7. UTF-8 (CJK + 4-byte emoji surrogate pair) & CRLF position accuracy
        crlf_path = root / "utf8_crlf.gsa"
        # Line 0: `def greet(n: Int): Int = n + 1\r\n`
        # Line 1: `def main(): Void = { let _ = "你好🚀"; let v = greet(7); () }\r\n`
        # UTF-16 columns on line 1:
        # `def main(): Void = { let _ = "` -> 30 chars
        # `你` (1) + `好` (1) + `🚀` (2) = 4 UTF-16 units -> col 34
        # `"; let v = ` -> 11 chars -> `greet` starts at UTF-16 col 45!
        crlf_src = "def greet(n: Int): Int = n + 1\r\ndef main(): Void = { let _ = \"你好🚀\"; let v = greet(7); () }\r\n"
        crlf_path.write_bytes(crlf_src.encode("utf-8"))
        crlf_uri = path_to_uri(crlf_path)
        client.notify("textDocument/didOpen", {
            "textDocument": {"uri": crlf_uri, "languageId": "geisha", "version": 1, "text": crlf_src},
        })
        diag_crlf = client.wait_diag_for(crlf_uri)
        assert diag_crlf == [], f"unexpected CRLF diagnostics: {diag_crlf}"
        def_utf8 = client.request("textDocument/definition", {
            "textDocument": {"uri": crlf_uri},
            "position": {"line": 1, "character": 46},
        })
        assert def_utf8["result"] is not None, "UTF-8/CRLF definition returned null"
        assert def_utf8["result"]["range"]["start"]["line"] == 0, f"unexpected UTF-8/CRLF def: {def_utf8}"

        # 8. didChange with type error -> publishDiagnostics with exact line & severity 1
        client.notifications.clear()
        bad_src = (
            "def main(): Void = {\n"
            "    let bad: Int = \"oops\";\n"
            "    ()\n"
            "}\n"
        )
        client.notify("textDocument/didChange", {
            "textDocument": {"uri": main_uri, "version": 3},
            "contentChanges": [{"text": bad_src}],
        })
        diags = client.wait_diag_for(main_uri)
        assert len(diags) == 1 and diags[0]["severity"] == 1 and diags[0]["source"] == "geisha"
        assert diags[0]["range"]["start"]["line"] == 1
        assert "Int" in diags[0]["message"] and "String" in diags[0]["message"]

        # 9. didChange back to valid -> clears diagnostics
        client.notify("textDocument/didChange", {
            "textDocument": {"uri": main_uri, "version": 4},
            "contentChanges": [{"text": main_src}],
        })
        diag_clear = client.wait_diag_for(main_uri)
        assert diag_clear == []

        # 10. unknown method -> -32601
        unk = client.request("geisha/nonExistentMethod", {})
        assert unk["error"]["code"] == -32601

        # 11. didClose removes cached doc state (subsequent hover returns null)
        client.notify("textDocument/didClose", {"textDocument": {"uri": main_uri}})
        _ = client.wait_diag_for(main_uri)
        hover_after_close = client.request("textDocument/hover", {
            "textDocument": {"uri": main_uri},
            "position": {"line": 25, "character": 18},
        })
        assert hover_after_close["result"] is None, f"expected null hover after didClose, got: {hover_after_close}"

        # 11b. Project `tests/spec.gsa` importing own package (`use demo_lib.hello`) -> 0 diagnostics, cross-file def, no geisha.lock written
        proj_dir = root / "demo_lib_proj"
        (proj_dir / "src").mkdir(parents=True)
        (proj_dir / "tests").mkdir(parents=True)
        (proj_dir / "geisha.toml").write_text('name = "demo_lib"\nversion = "0.1.0"\n', encoding="utf-8")
        lib_path = proj_dir / "src" / "demo_lib.gsa"
        lib_path.write_text("/// Return 42.\npub def hello(): Int = 42\n", encoding="utf-8")
        spec_path = proj_dir / "tests" / "spec.gsa"
        spec_src = "use demo_lib.hello\n\ndef main(): Void = {\n    let v = hello();\n    ()\n}\n"
        spec_path.write_text(spec_src, encoding="utf-8")
        spec_uri = path_to_uri(spec_path)
        lib_uri = path_to_uri(lib_path)
        client.notify("textDocument/didOpen", {
            "textDocument": {"uri": spec_uri, "languageId": "geisha", "version": 1, "text": spec_src},
        })
        diag_spec = client.wait_diag_for(spec_uri)
        assert diag_spec == [], f"expected 0 diagnostics for self-pkg test import, got: {diag_spec}"
        assert not (proj_dir / "geisha.lock").exists(), "LSP must not write geisha.lock during read-only analysis"
        def_self = client.request("textDocument/definition", {
            "textDocument": {"uri": spec_uri},
            "position": {"line": 3, "character": 13},
        })
        assert def_self["result"] is not None and def_self["result"]["uri"] == lib_uri, f"expected def in {lib_uri}, got: {def_self}"

        # 11c. Multi-file unsaved in-memory overlay & dependency diagnostic URI attribution
        ov_dir = root / "overlay_proj"
        ov_dir.mkdir(parents=True)
        a_path = ov_dir / "a.gsa"
        b_path = ov_dir / "b.gsa"
        a_disk = "pub def value(): Int = 42\n"
        b_src = "use a.value\n\ndef main(): Void = {\n    let s: String = value();\n    ()\n}\n"
        a_path.write_text(a_disk, encoding="utf-8")
        b_path.write_text(b_src, encoding="utf-8")
        a_uri = path_to_uri(a_path)
        b_uri = path_to_uri(b_path)

        client.notify("textDocument/didOpen", {
            "textDocument": {"uri": a_uri, "languageId": "geisha", "version": 1, "text": a_disk},
        })
        assert client.wait_diag_for(a_uri) == []
        client.notify("textDocument/didOpen", {
            "textDocument": {"uri": b_uri, "languageId": "geisha", "version": 1, "text": b_src},
        })
        b_diags_init = client.wait_diag_for(b_uri)
        assert len(b_diags_init) == 1 and "Int" in b_diags_init[0]["message"], f"expected Int/String mismatch in b.gsa, got: {b_diags_init}"

        # Unsaved edit to a.gsa changes return type to String -> b.gsa diagnostics automatically clear!
        client.notifications.clear()
        a_unsaved_ok = "pub def value(): String = \"ok\"\n"
        client.notify("textDocument/didChange", {
            "textDocument": {"uri": a_uri, "version": 2},
            "contentChanges": [{"text": a_unsaved_ok}],
        })
        assert client.wait_diag_for(a_uri) == []
        assert client.wait_diag_for(b_uri) == [], "expected b.gsa diagnostics to clear using unsaved a.gsa overlay"

        # Unsaved type error in a.gsa -> error attributed to a.gsa URI, b.gsa stays clean
        client.notifications.clear()
        a_unsaved_err = "pub def value(): String = 999\n"
        client.notify("textDocument/didChange", {
            "textDocument": {"uri": a_uri, "version": 3},
            "contentChanges": [{"text": a_unsaved_err}],
        })
        a_err_diags = client.wait_diag_for(a_uri)
        assert len(a_err_diags) == 1 and a_err_diags[0]["range"]["start"]["line"] == 0, f"expected error on a.gsa: {a_err_diags}"
        b_clean = client.wait_diag_for(b_uri)
        assert b_clean == [], f"expected dependency error attributed to a.gsa rather than b.gsa, got: {b_clean}"

        # 11d. Directory symlink project: unsaved overlay still hits canonical path & preserves client symlink URI
        real_proj = root / "real_sym_proj"
        (real_proj / "src").mkdir(parents=True)
        (real_proj / "geisha.toml").write_text('name = "sym_proj"\nversion = "0.1.0"\n', encoding="utf-8")
        (real_proj / "src" / "dep.gsa").write_text("pub def msg(): Int = 1\n", encoding="utf-8")
        app_src = "use dep.msg\n\ndef main(): Void = {\n    let s: String = msg();\n    ()\n}\n"
        (real_proj / "src" / "app.gsa").write_text(app_src, encoding="utf-8")
        link_proj = root / "link_sym_proj"
        os.symlink(real_proj, link_proj)
        # Deliberately construct non-resolved symlink URIs (just like VS Code opening a symlinked folder)
        dep_link_uri = "file://" + str(link_proj / "src" / "dep.gsa")
        app_link_uri = "file://" + str(link_proj / "src" / "app.gsa")

        client.notifications.clear()
        client.notify("textDocument/didOpen", {
            "textDocument": {"uri": dep_link_uri, "languageId": "geisha", "version": 1, "text": "pub def msg(): Int = 1\n"},
        })
        assert client.wait_diag_for(dep_link_uri) == []
        client.notify("textDocument/didOpen", {
            "textDocument": {"uri": app_link_uri, "languageId": "geisha", "version": 1, "text": app_src},
        })
        app_init = client.wait_diag_for(app_link_uri)
        assert len(app_init) == 1 and "Int" in app_init[0]["message"], f"expected Int/String error via symlink, got: {app_init}"

        # Unsaved edit via symlink URI updates canonical overlay -> app.gsa via symlink clears!
        # Also shift `msg` to line 2 in the unsaved buffer so definition verifies BOTH symlink URI & unsaved range!
        client.notifications.clear()
        client.notify("textDocument/didChange", {
            "textDocument": {"uri": dep_link_uri, "version": 2},
            "contentChanges": [{"text": "// shifted in unsaved buffer\n\npub def msg(): String = \"ok\"\n"}],
        })
        assert client.wait_diag_for(dep_link_uri) == []
        assert client.wait_diag_for(app_link_uri) == [], "expected symlinked app.gsa to clear via canonicalized overlay"
        def_sym = client.request("textDocument/definition", {
            "textDocument": {"uri": app_link_uri},
            "position": {"line": 3, "character": 22},
        })
        assert def_sym["result"] is not None, "symlink cross-file definition returned null"
        assert def_sym["result"]["uri"] == dep_link_uri, f"expected symlink URI {dep_link_uri}, got {def_sym}"
        assert def_sym["result"]["range"]["start"]["line"] == 2, f"expected unsaved buffer line 2, got {def_sym}"

        # Unsaved error in symlinked dep.gsa -> diagnostic preserves client's symlink URI
        client.notifications.clear()
        client.notify("textDocument/didChange", {
            "textDocument": {"uri": dep_link_uri, "version": 3},
            "contentChanges": [{"text": "pub def msg(): String = 123\n"}],
        })
        dep_link_err = client.wait_diag_for(dep_link_uri)
        assert len(dep_link_err) == 1 and dep_link_err[0]["range"]["start"]["line"] == 0, f"expected error on symlink URI {dep_link_uri}: {dep_link_err}"
        assert client.wait_diag_for(app_link_uri) == []

        # 11e. Scope-aware references & rename (shadowing, sibling functions, struct fields, cross-file & unsaved overlay)
        ref_dir = root / "refactor_proj"
        ref_dir.mkdir(parents=True)
        lib_ref_path = ref_dir / "geom.gsa"
        lib_ref_src = (
            "pub data Vec2 { x: Int, y: Int }\n"
            "pub data Other { x: Int }\n"
            "pub data Color {\n"
            "    Red,\n"
            "    Blue(Int),\n"
            "}\n"
            "pub def scale(v: Vec2, factor: Int): Int = v.x * factor + v.y\n"
        )
        app_ref_path = ref_dir / "app.gsa"
        app_ref_src = (
            "use geom.{Vec2, Other, Color, Red, Blue, scale}\n"
            "\n"
            "def scopedShadow(): Int = {\n"
            "    let x = 1;\n"
            "    let y = x + 2;\n"
            "    let x = 10;\n"
            "    x + y\n"
            "}\n"
            "\n"
            "def siblingScope(): Int = {\n"
            "    let x = 99;\n"
            "    x\n"
            "}\n"
            "\n"
            "def useGeom(c: Color): Int = {\n"
            "    let p = Vec2 { x: 3, y: 4 };\n"
            "    let o = Other { x: 5 };\n"
            "    let explicit: Int = p.x + o.x;\n"
            "    let res = scale(p, 2) + explicit;\n"
            "    match c {\n"
            "        Red -> res,\n"
            "        Blue(n) -> res + n,\n"
            "    }\n"
            "}\n"
        )
        lib_ref_path.write_text(lib_ref_src, encoding="utf-8")
        app_ref_path.write_text(app_ref_src, encoding="utf-8")
        lib_ref_uri = path_to_uri(lib_ref_path)
        app_ref_uri = path_to_uri(app_ref_path)

        client.notifications.clear()
        client.notify("textDocument/didOpen", {
            "textDocument": {"uri": lib_ref_uri, "languageId": "geisha", "version": 1, "text": lib_ref_src},
        })
        assert client.wait_diag_for(lib_ref_uri) == []
        client.notify("textDocument/didOpen", {
            "textDocument": {"uri": app_ref_uri, "languageId": "geisha", "version": 1, "text": app_ref_src},
        })
        assert client.wait_diag_for(app_ref_uri) == []

        # References on outer `x` (line 3, col 8: `let x = 1;`): only line 3 & line 4 (NOT line 5/6 or sibling line 10/11)
        refs_outer_incl = client.request("textDocument/references", {
            "textDocument": {"uri": app_ref_uri},
            "position": {"line": 3, "character": 8},
            "context": {"includeDeclaration": True},
        })
        outer_lines = sorted(r["range"]["start"]["line"] for r in refs_outer_incl["result"])
        assert outer_lines == [3, 4], f"expected outer x refs on lines [3, 4], got {refs_outer_incl}"

        refs_outer_excl = client.request("textDocument/references", {
            "textDocument": {"uri": app_ref_uri},
            "position": {"line": 3, "character": 8},
            "context": {"includeDeclaration": False},
        })
        outer_excl_lines = sorted(r["range"]["start"]["line"] for r in refs_outer_excl["result"])
        assert outer_excl_lines == [4], f"expected outer x refs (excl decl) on [4], got {refs_outer_excl}"

        # References on inner shadowed `x` (line 5, col 8): only lines 5 & 6
        refs_inner = client.request("textDocument/references", {
            "textDocument": {"uri": app_ref_uri},
            "position": {"line": 5, "character": 8},
            "context": {"includeDeclaration": True},
        })
        inner_lines = sorted(r["range"]["start"]["line"] for r in refs_inner["result"])
        assert inner_lines == [5, 6], f"expected inner x refs on [5, 6], got {refs_inner}"

        # References on Vec2.x field (line 17, col 26: `p.x`): geom.gsa decl + v.x + app.gsa Vec2{x:3} + p.x (NOT Other.x!)
        refs_field = client.request("textDocument/references", {
            "textDocument": {"uri": app_ref_uri},
            "position": {"line": 17, "character": 26},
            "context": {"includeDeclaration": True},
        })
        field_uris_lines = sorted((r["uri"], r["range"]["start"]["line"]) for r in refs_field["result"])
        assert (lib_ref_uri, 0) in field_uris_lines and (lib_ref_uri, 6) in field_uris_lines, f"missing geom.gsa Vec2.x refs: {field_uris_lines}"
        assert (app_ref_uri, 15) in field_uris_lines and (app_ref_uri, 17) in field_uris_lines, f"missing app.gsa Vec2.x refs: {field_uris_lines}"
        assert (lib_ref_uri, 1) not in field_uris_lines and (app_ref_uri, 16) not in field_uris_lines, f"Other.x leaked into Vec2.x refs: {field_uris_lines}"

        # prepareRename: rejects keyword `let`, accepts `scale`
        prep_kw = client.request("textDocument/prepareRename", {
            "textDocument": {"uri": app_ref_uri},
            "position": {"line": 3, "character": 5},
        })
        assert prep_kw["result"] is None, f"expected null prepareRename on keyword 'let', got {prep_kw}"

        prep_scale = client.request("textDocument/prepareRename", {
            "textDocument": {"uri": app_ref_uri},
            "position": {"line": 18, "character": 16},
        })
        assert prep_scale["result"] is not None and prep_scale["result"]["placeholder"] == "scale", f"unexpected prepareRename: {prep_scale}"

        # rename: rejects keyword and invalid identifier with -32602
        bad_ren_kw = client.request("textDocument/rename", {
            "textDocument": {"uri": app_ref_uri},
            "position": {"line": 18, "character": 16},
            "newName": "match",
        })
        assert "error" in bad_ren_kw and bad_ren_kw["error"]["code"] == -32602, f"expected -32602 for keyword rename: {bad_ren_kw}"

        bad_ren_id = client.request("textDocument/rename", {
            "textDocument": {"uri": app_ref_uri},
            "position": {"line": 18, "character": 16},
            "newName": "123bad",
        })
        assert "error" in bad_ren_id and bad_ren_id["error"]["code"] == -32602, f"expected -32602 for invalid ident rename: {bad_ren_id}"

        # Cross-file rename of `scale` -> `scaleVec` across geom.gsa and app.gsa
        ren_scale = client.request("textDocument/rename", {
            "textDocument": {"uri": app_ref_uri},
            "position": {"line": 18, "character": 16},
            "newName": "scaleVec",
        })
        changes_scale = ren_scale["result"]["changes"]
        assert lib_ref_uri in changes_scale and app_ref_uri in changes_scale, f"expected cross-file rename edits: {changes_scale}"
        assert len(changes_scale[lib_ref_uri]) == 1 and changes_scale[lib_ref_uri][0]["newText"] == "scaleVec"
        assert len(changes_scale[app_ref_uri]) == 2, f"expected import + call edits in app.gsa, got: {changes_scale[app_ref_uri]}"

        # Cross-file rename of enum variant `Blue` -> `Cyan`
        ren_var = client.request("textDocument/rename", {
            "textDocument": {"uri": app_ref_uri},
            "position": {"line": 21, "character": 10},
            "newName": "Cyan",
        })
        changes_var = ren_var["result"]["changes"]
        assert lib_ref_uri in changes_var and app_ref_uri in changes_var, f"expected cross-file variant rename: {changes_var}"

        # Unsaved overlay cross-file rename: add another call to `scale` in unsaved app.gsa buffer
        app_ref_unsaved = app_ref_src + "\ndef extraCall(v: Vec2): Int = scale(v, 3)\n"
        client.notify("textDocument/didChange", {
            "textDocument": {"uri": app_ref_uri, "version": 2},
            "contentChanges": [{"text": app_ref_unsaved}],
        })
        assert client.wait_diag_for(app_ref_uri) == []
        ren_overlay = client.request("textDocument/rename", {
            "textDocument": {"uri": lib_ref_uri},
            "position": {"line": 6, "character": 9},
            "newName": "scaleVec",
        })
        assert len(ren_overlay["result"]["changes"][app_ref_uri]) == 3, f"expected 3 edits in unsaved overlay app.gsa, got: {ren_overlay}"

        # 11f. Inlay Hints: inferred `let` types (skipping explicit annotations) & function call parameter names
        hints_resp = client.request("textDocument/inlayHint", {
            "textDocument": {"uri": app_ref_uri},
            "range": {"start": {"line": 14, "character": 0}, "end": {"line": 23, "character": 0}},
        })
        hints = hints_resp["result"]
        type_hints = [(h["position"]["line"], h["label"]) for h in hints if h["kind"] == 1]
        param_hints = [(h["position"]["line"], h["label"]) for h in hints if h["kind"] == 2]
        assert any(l == 15 and "Vec2" in lbl for l, lbl in type_hints), f"expected Vec2 inlay hint on line 15: {type_hints}"
        assert any(l == 18 and "Int" in lbl for l, lbl in type_hints), f"expected Int inlay hint on line 18: {type_hints}"
        assert not any(l == 17 for l, _ in type_hints), f"explicitly annotated `let explicit: Int` on line 17 must not get type hint: {type_hints}"
        assert (18, "v:") in param_hints and (18, "factor:") in param_hints, f"expected parameter hints v: and factor: on line 18: {param_hints}"

        # 11g. Code Actions (Quick Fixes): unused var prefix `_`, missing match arm skeleton, auto-import
        qa_dir = root / "quickfix_proj"
        qa_dir.mkdir(parents=True)
        (qa_dir / "myutil.gsa").write_text("pub def magicNum(): Int = 77\n", encoding="utf-8")

        # 11g-1: Unused variable -> prefix `_`
        unused_path = qa_dir / "unused.gsa"
        unused_src = "def f(): Int = {\n    let temp = 42;\n    1\n}\n"
        unused_path.write_text(unused_src, encoding="utf-8")
        unused_uri = path_to_uri(unused_path)
        client.notify("textDocument/didOpen", {
            "textDocument": {"uri": unused_uri, "languageId": "geisha", "version": 1, "text": unused_src},
        })
        assert client.wait_diag_for(unused_uri) == []
        ca_unused = client.request("textDocument/codeAction", {
            "textDocument": {"uri": unused_uri},
            "range": {"start": {"line": 1, "character": 8}, "end": {"line": 1, "character": 12}},
            "context": {"diagnostics": []},
        })
        unused_actions = ca_unused["result"]
        assert any("_temp" in a["edit"]["changes"][unused_uri][0]["newText"] for a in unused_actions), f"expected _temp quickfix: {unused_actions}"

        # 11g-2: Missing match branch skeleton
        match_path = qa_dir / "missing_match.gsa"
        match_src = (
            "data Toggle { On, Off }\n"
            "def f(t: Toggle): Void = match t {\n"
            "    On -> (),\n"
            "}\n"
        )
        match_path.write_text(match_src, encoding="utf-8")
        match_uri = path_to_uri(match_path)
        client.notify("textDocument/didOpen", {
            "textDocument": {"uri": match_uri, "languageId": "geisha", "version": 1, "text": match_src},
        })
        match_diags = client.wait_diag_for(match_uri)
        assert len(match_diags) == 1 and "Off" in match_diags[0]["message"], f"expected missing Off diag: {match_diags}"
        ca_match = client.request("textDocument/codeAction", {
            "textDocument": {"uri": match_uri},
            "range": match_diags[0]["range"],
            "context": {"diagnostics": match_diags},
        })
        match_actions = ca_match["result"]
        assert any("Off -> ()" in a["edit"]["changes"][match_uri][0]["newText"] for a in match_actions), f"expected missing match arm quickfix: {match_actions}"

        # 11g-3: Missing symbol auto-import (both builtin std.str and sibling myutil)
        imp_path = qa_dir / "missing_imp.gsa"
        imp_src = "def f(): String = intToStr(1)\n"
        imp_path.write_text(imp_src, encoding="utf-8")
        imp_uri = path_to_uri(imp_path)
        client.notify("textDocument/didOpen", {
            "textDocument": {"uri": imp_uri, "languageId": "geisha", "version": 1, "text": imp_src},
        })
        imp_diags = client.wait_diag_for(imp_uri)
        assert len(imp_diags) == 1 and "intToStr" in imp_diags[0]["message"], f"expected undefined intToStr diag: {imp_diags}"
        ca_imp = client.request("textDocument/codeAction", {
            "textDocument": {"uri": imp_uri},
            "range": imp_diags[0]["range"],
            "context": {"diagnostics": imp_diags},
        })
        imp_actions = ca_imp["result"]
        assert any("use std.str.intToStr" in a["edit"]["changes"][imp_uri][0]["newText"] for a in imp_actions), f"expected std.str.intToStr auto-import: {imp_actions}"

        imp2_src = "def f(): Int = magicNum()\n"
        client.notify("textDocument/didChange", {
            "textDocument": {"uri": imp_uri, "version": 2},
            "contentChanges": [{"text": imp2_src}],
        })
        imp2_diags = client.wait_diag_for(imp_uri)
        assert len(imp2_diags) == 1 and "magicNum" in imp2_diags[0]["message"]
        ca_imp2 = client.request("textDocument/codeAction", {
            "textDocument": {"uri": imp_uri},
            "range": imp2_diags[0]["range"],
            "context": {"diagnostics": imp2_diags},
        })
        imp2_actions = ca_imp2["result"]
        assert any("use myutil.magicNum" in a["edit"]["changes"][imp_uri][0]["newText"] for a in imp2_actions), f"expected myutil.magicNum auto-import: {imp2_actions}"

        # 11h. Regression tests: variable capture rejection, same-name aliased imports across modules, nested module auto-import
        def apply_edits(text: str, edits: list[dict]) -> str:
            # Apply LSP TextEdits in reverse document order
            lines = text.splitlines(keepends=True)
            def pos_to_idx(l: int, c: int) -> int:
                return sum(len(lines[i]) for i in range(l)) + c
            indexed = sorted(
                ((pos_to_idx(e["range"]["start"]["line"], e["range"]["start"]["character"]),
                  pos_to_idx(e["range"]["end"]["line"], e["range"]["end"]["character"]),
                  e["newText"]) for e in edits),
                key=lambda x: (x[0], x[1]),
                reverse=True,
            )
            out = text
            for s, e, nt in indexed:
                out = out[:s] + nt + out[e:]
            return out

        # 11h-1: Variable capture rejection on rename (forward capture, reverse capture, duplicate param)
        cap_path = qa_dir / "capture.gsa"
        cap_src = (
            "def f(x: Int): Int = {\n"
            "    let y = 9;\n"
            "    x + y\n"
            "}\n"
            "def g(a: Int, b: Int): Int = a + b\n"
        )
        cap_path.write_text(cap_src, encoding="utf-8")
        cap_uri = path_to_uri(cap_path)
        client.notify("textDocument/didOpen", {
            "textDocument": {"uri": cap_uri, "languageId": "geisha", "version": 1, "text": cap_src},
        })
        assert client.wait_diag_for(cap_uri) == []
        # Rename param `x` -> `y` (would be captured by `let y = 9`)
        cap_fwd = client.request("textDocument/rename", {
            "textDocument": {"uri": cap_uri},
            "position": {"line": 0, "character": 6},
            "newName": "y",
        })
        assert "error" in cap_fwd and cap_fwd["error"]["code"] == -32602, f"expected -32602 on forward capture: {cap_fwd}"
        # Rename `let y` -> `x` (would capture param `x` in `x + y`)
        cap_rev = client.request("textDocument/rename", {
            "textDocument": {"uri": cap_uri},
            "position": {"line": 1, "character": 8},
            "newName": "x",
        })
        assert "error" in cap_rev and cap_rev["error"]["code"] == -32602, f"expected -32602 on reverse capture: {cap_rev}"
        # Rename param `a` -> `b` (duplicate parameter)
        cap_dup = client.request("textDocument/rename", {
            "textDocument": {"uri": cap_uri},
            "position": {"line": 4, "character": 6},
            "newName": "b",
        })
        assert "error" in cap_dup and cap_dup["error"]["code"] == -32602, f"expected -32602 on duplicate param: {cap_dup}"

        # 11h-2: Cross-file same-named imports with explicit `as` aliases (`use a.{load as loadA}` + `use b.{load as loadB}`)
        al_dir = root / "alias_proj"
        al_dir.mkdir(parents=True)
        ma_path = al_dir / "a.gsa"
        mb_path = al_dir / "b.gsa"
        mmain_path = al_dir / "main.gsa"
        ma_src = "pub def load(): Int = 1\n"
        mb_src = "pub def load(): Int = 2\n"
        mmain_src = (
            "use a.{load as loadA}\n"
            "use b.{load as loadB}\n"
            "def main(): Int = loadA() + loadB()\n"
        )
        ma_path.write_text(ma_src, encoding="utf-8")
        mb_path.write_text(mb_src, encoding="utf-8")
        mmain_path.write_text(mmain_src, encoding="utf-8")
        ma_uri = path_to_uri(ma_path)
        mb_uri = path_to_uri(mb_path)
        mmain_uri = path_to_uri(mmain_path)
        client.notifications.clear()
        for u, t in ((ma_uri, ma_src), (mb_uri, mb_src), (mmain_uri, mmain_src)):
            client.notify("textDocument/didOpen", {
                "textDocument": {"uri": u, "languageId": "geisha", "version": 1, "text": t},
            })
            assert client.wait_diag_for(u) == []

        # References on `a.load` must NOT include `b.gsa` or line 1 (`use b.{load as loadB}`)
        refs_a = client.request("textDocument/references", {
            "textDocument": {"uri": ma_uri},
            "position": {"line": 0, "character": 8},
            "context": {"includeDeclaration": True},
        })
        refs_a_uris = {r["uri"] for r in refs_a["result"]}
        assert mb_uri not in refs_a_uris, f"b.gsa leaked into a.load references: {refs_a}"
        mmain_ref_lines = sorted(r["range"]["start"]["line"] for r in refs_a["result"] if r["uri"] == mmain_uri)
        assert mmain_ref_lines == [0, 2], f"expected a.load refs in main.gsa on lines [0, 2], got {refs_a}"

        # Rename `a.load` -> `fetchA`: only rewrites `a.gsa` and `load` in `use a.{load as loadA}`, preserving `loadA` and leaving `b` untouched!
        ren_a = client.request("textDocument/rename", {
            "textDocument": {"uri": ma_uri},
            "position": {"line": 0, "character": 8},
            "newName": "fetchA",
        })
        ch_a = ren_a["result"]["changes"]
        assert mb_uri not in ch_a, f"b.gsa must not be edited when renaming a.load: {ch_a}"
        new_ma = apply_edits(ma_src, ch_a[ma_uri])
        new_mmain = apply_edits(mmain_src, ch_a[mmain_uri])
        assert new_ma == "pub def fetchA(): Int = 1\n", f"unexpected renamed a.gsa: {new_ma!r}"
        assert new_mmain == (
            "use a.{fetchA as loadA}\n"
            "use b.{load as loadB}\n"
            "def main(): Int = loadA() + loadB()\n"
        ), f"unexpected renamed main.gsa: {new_mmain!r}"
        # Verify renamed files typecheck cleanly with 0 diagnostics!
        client.notifications.clear()
        client.notify("textDocument/didChange", {"textDocument": {"uri": ma_uri, "version": 2}, "contentChanges": [{"text": new_ma}]})
        assert client.wait_diag_for(ma_uri) == []
        client.notify("textDocument/didChange", {"textDocument": {"uri": mmain_uri, "version": 2}, "contentChanges": [{"text": new_mmain}]})
        assert client.wait_diag_for(mmain_uri) == []

        # 11h-3: Nested module auto-import quick fix (`src/nested/helper.gsa` -> `use nested.helper.widgetMagic`) + verify 0 diagnostics after applying!
        nest_dir = root / "nested_imp_proj"
        (nest_dir / "src" / "nested").mkdir(parents=True)
        (nest_dir / "geisha.toml").write_text('name = "nested_imp"\nversion = "0.1.0"\n', encoding="utf-8")
        (nest_dir / "src" / "nested" / "helper.gsa").write_text("pub def widgetMagic(): Int = 88\n", encoding="utf-8")
        nmain_path = nest_dir / "src" / "main.gsa"
        nmain_src = "def main(): Int = widgetMagic()\n"
        nmain_path.write_text(nmain_src, encoding="utf-8")
        nmain_uri = path_to_uri(nmain_path)
        client.notifications.clear()
        client.notify("textDocument/didOpen", {
            "textDocument": {"uri": nmain_uri, "languageId": "geisha", "version": 1, "text": nmain_src},
        })
        ndiags = client.wait_diag_for(nmain_uri)
        assert len(ndiags) == 1 and "widgetMagic" in ndiags[0]["message"]
        ca_nest = client.request("textDocument/codeAction", {
            "textDocument": {"uri": nmain_uri},
            "range": ndiags[0]["range"],
            "context": {"diagnostics": ndiags},
        })
        nest_act = next(
            (a for a in ca_nest["result"] if "use nested.helper.widgetMagic" in a["edit"]["changes"][nmain_uri][0]["newText"]),
            None,
        )
        assert nest_act is not None, f"expected nested.helper auto-import quickfix, got: {ca_nest}"
        fixed_nmain = apply_edits(nmain_src, nest_act["edit"]["changes"][nmain_uri])
        client.notify("textDocument/didChange", {
            "textDocument": {"uri": nmain_uri, "version": 2},
            "contentChanges": [{"text": fixed_nmain}],
        })
        assert client.wait_diag_for(nmain_uri) == [], f"applied nested auto-import still has diagnostics! source:\n{fixed_nmain}"

        # 11h-4: Recursive type self-reference preserved when includeDeclaration=False, and type rename does NOT touch unrelated expression bodies
        rec_path = qa_dir / "rec_type.gsa"
        rec_src = (
            "use std.option.{Option, Some, None}\n"
            "data Node { val: Int, next: Option Node }\n"
            "def f(n: Node): Int = n.val\n"
        )
        rec_path.write_text(rec_src, encoding="utf-8")
        rec_uri = path_to_uri(rec_path)
        client.notify("textDocument/didOpen", {
            "textDocument": {"uri": rec_uri, "languageId": "geisha", "version": 1, "text": rec_src},
        })
        assert client.wait_diag_for(rec_uri) == []
        refs_rec_excl = client.request("textDocument/references", {
            "textDocument": {"uri": rec_uri},
            "position": {"line": 1, "character": 6},
            "context": {"includeDeclaration": False},
        })
        rec_excl_positions = sorted((r["range"]["start"]["line"], r["range"]["start"]["character"]) for r in refs_rec_excl["result"])
        assert (1, 35) in rec_excl_positions and (2, 9) in rec_excl_positions, f"expected recursive self-ref (1,35) & sig ref (2,9), got {rec_excl_positions}"
        assert (1, 5) not in rec_excl_positions, f"declaration header (1,5) must be excluded when includeDeclaration=False: {rec_excl_positions}"

        # 11h-5: Top-level same-module rename collision rejected (-32602)
        col_path = qa_dir / "collision.gsa"
        col_src = "def first(): Int = 1\ndef second(): Int = 2\ndef main(): Int = first() + second()\n"
        col_path.write_text(col_src, encoding="utf-8")
        col_uri = path_to_uri(col_path)
        client.notify("textDocument/didOpen", {
            "textDocument": {"uri": col_uri, "languageId": "geisha", "version": 1, "text": col_src},
        })
        assert client.wait_diag_for(col_uri) == []
        col_ren = client.request("textDocument/rename", {
            "textDocument": {"uri": col_uri},
            "position": {"line": 0, "character": 5},
            "newName": "second",
        })
        assert "error" in col_ren and col_ren["error"]["code"] == -32602, f"expected -32602 on top-level collision: {col_ren}"

        # 11h-6: `UseAlias` (`use m1.load as loadA`), multi-line `UseMulti` with comments (`use m1.{\n // comment\n load as chosen,\n}`),
        # and multi-line string containing `use m1.load as example` (must NOT be modified!)
        ml_dir = root / "multiline_alias_proj"
        ml_dir.mkdir(parents=True)
        m1_path = ml_dir / "m1.gsa"
        u1_path = ml_dir / "u1.gsa"
        u2_path = ml_dir / "u2.gsa"
        m1_src = "pub def load(): Int = 7\n"
        u1_src = (
            "use m1.load as loadA\n"
            "def f(): Int = {\n"
            "    let doc = \"example:\\nuse m1.load as example\\n\";\n"
            "    let _ = doc;\n"
            "    loadA()\n"
            "}\n"
        )
        u2_src = (
            "use m1.{\n"
            "    // comment before imported symbol\n"
            "    load as chosen,\n"
            "}\n"
            "pub mod inner {\n"
            "    use m1.load as innerLoad\n"
            "    pub def h(): Int = innerLoad()\n"
            "}\n"
            "def g(): Int = chosen() + inner.h()\n"
        )
        m1_path.write_text(m1_src, encoding="utf-8")
        u1_path.write_text(u1_src, encoding="utf-8")
        u2_path.write_text(u2_src, encoding="utf-8")
        m1_uri = path_to_uri(m1_path)
        u1_uri = path_to_uri(u1_path)
        u2_uri = path_to_uri(u2_path)
        client.notifications.clear()
        for u, t in ((m1_uri, m1_src), (u1_uri, u1_src), (u2_uri, u2_src)):
            client.notify("textDocument/didOpen", {
                "textDocument": {"uri": u, "languageId": "geisha", "version": 1, "text": t},
            })
            assert client.wait_diag_for(u) == []
        ren_ml = client.request("textDocument/rename", {
            "textDocument": {"uri": m1_uri},
            "position": {"line": 0, "character": 8},
            "newName": "loadV2",
        })
        ch_ml = ren_ml["result"]["changes"]
        new_m1 = apply_edits(m1_src, ch_ml[m1_uri])
        new_u1 = apply_edits(u1_src, ch_ml[u1_uri])
        new_u2 = apply_edits(u2_src, ch_ml[u2_uri])
        assert new_m1 == "pub def loadV2(): Int = 7\n", f"unexpected m1: {new_m1!r}"
        assert new_u1 == (
            "use m1.loadV2 as loadA\n"
            "def f(): Int = {\n"
            "    let doc = \"example:\\nuse m1.load as example\\n\";\n"
            "    let _ = doc;\n"
            "    loadA()\n"
            "}\n"
        ), f"unexpected u1 (string literal must NOT be modified!): {new_u1!r}"
        assert new_u2 == (
            "use m1.{\n"
            "    // comment before imported symbol\n"
            "    loadV2 as chosen,\n"
            "}\n"
            "pub mod inner {\n"
            "    use m1.loadV2 as innerLoad\n"
            "    pub def h(): Int = innerLoad()\n"
            "}\n"
            "def g(): Int = chosen() + inner.h()\n"
        ), f"unexpected u2: {new_u2!r}"
        client.notifications.clear()
        for u, t in ((m1_uri, new_m1), (u1_uri, new_u1), (u2_uri, new_u2)):
            client.notify("textDocument/didChange", {"textDocument": {"uri": u, "version": 2}, "contentChanges": [{"text": t}]})
            assert client.wait_diag_for(u) == []

        # 11h-7: Inline `ModSub` lexical scope conflict check:
        # (a) Unaliased `use m2.load` + `def fetchA` in same `pub mod inner` -> rejected (-32602)
        # (b) `def fetchA` in independent sibling `pub mod other` -> allowed!
        # (c) Aliased `use m2.load as loadA` + `def fetchA` in same `pub mod inner` -> allowed!
        ms_dir = root / "modsub_conflict_proj"
        ms_dir.mkdir(parents=True)
        m2_path = ms_dir / "m2.gsa"
        ms_user_path = ms_dir / "ms_user.gsa"
        m2_src = "pub def load(): Int = 7\n"
        ms_conflict_src = (
            "pub mod inner {\n"
            "    use m2.load\n"
            "    def fetchA(): Int = 93\n"
            "    pub def run(): Int = load() + fetchA()\n"
            "}\n"
        )
        m2_path.write_text(m2_src, encoding="utf-8")
        ms_user_path.write_text(ms_conflict_src, encoding="utf-8")
        m2_uri = path_to_uri(m2_path)
        ms_user_uri = path_to_uri(ms_user_path)
        client.notifications.clear()
        client.notify("textDocument/didOpen", {"textDocument": {"uri": m2_uri, "languageId": "geisha", "version": 1, "text": m2_src}})
        assert client.wait_diag_for(m2_uri) == []
        client.notify("textDocument/didOpen", {"textDocument": {"uri": ms_user_uri, "languageId": "geisha", "version": 1, "text": ms_conflict_src}})
        assert client.wait_diag_for(ms_user_uri) == []

        # (a) Same ModSub conflict -> must reject with -32602
        ren_ms_bad = client.request("textDocument/rename", {
            "textDocument": {"uri": m2_uri},
            "position": {"line": 0, "character": 8},
            "newName": "fetchA",
        })
        assert "error" in ren_ms_bad and ren_ms_bad["error"]["code"] == -32602, f"expected -32602 on ModSub unaliased conflict: {ren_ms_bad}"

        # (b) Independent sibling ModSub with `fetchA` -> allowed!
        ms_sibling_src = (
            "pub mod inner {\n"
            "    use m2.load\n"
            "    pub def run(): Int = load()\n"
            "}\n"
            "pub mod other {\n"
            "    pub def fetchA(): Int = 93\n"
            "}\n"
        )
        client.notifications.clear()
        client.notify("textDocument/didChange", {"textDocument": {"uri": ms_user_uri, "version": 2}, "contentChanges": [{"text": ms_sibling_src}]})
        assert client.wait_diag_for(ms_user_uri) == []
        ren_ms_sib = client.request("textDocument/rename", {
            "textDocument": {"uri": m2_uri},
            "position": {"line": 0, "character": 8},
            "newName": "fetchA",
        })
        assert "result" in ren_ms_sib and ms_user_uri in ren_ms_sib["result"]["changes"], f"expected sibling ModSub rename allowed: {ren_ms_sib}"

        # (c) Explicit alias `use m2.load as loadA` + `def fetchA` in same ModSub -> allowed!
        ms_alias_src = (
            "pub mod inner {\n"
            "    use m2.load as loadA\n"
            "    def fetchA(): Int = 93\n"
            "    pub def run(): Int = loadA() + fetchA()\n"
            "}\n"
        )
        client.notifications.clear()
        client.notify("textDocument/didChange", {"textDocument": {"uri": ms_user_uri, "version": 3}, "contentChanges": [{"text": ms_alias_src}]})
        assert client.wait_diag_for(ms_user_uri) == []
        ren_ms_al = client.request("textDocument/rename", {
            "textDocument": {"uri": m2_uri},
            "position": {"line": 0, "character": 8},
            "newName": "fetchA",
        })
        assert "result" in ren_ms_al and ms_user_uri in ren_ms_al["result"]["changes"], f"expected aliased ModSub rename allowed: {ren_ms_al}"
        new_ms_al = apply_edits(ms_alias_src, ren_ms_al["result"]["changes"][ms_user_uri])
        assert "use m2.fetchA as loadA" in new_ms_al and "loadA() + fetchA()" in new_ms_al, f"unexpected aliased ModSub rename: {new_ms_al!r}"

        # (d) `open m2` (`UseGlob`) + `def fetchA` in same scope -> rejected (-32602)
        extra_path = ms_dir / "extra.gsa"
        extra_src = "pub def fetchA(): Int = 93\n"
        extra_path.write_text(extra_src, encoding="utf-8")
        ms_open_target_src = (
            "pub mod inner {\n"
            "    open m2\n"
            "    def fetchA(): Int = 93\n"
            "    pub def run(): Int = load() + fetchA()\n"
            "}\n"
        )
        client.notifications.clear()
        client.notify("textDocument/didChange", {"textDocument": {"uri": ms_user_uri, "version": 4}, "contentChanges": [{"text": ms_open_target_src}]})
        assert client.wait_diag_for(ms_user_uri) == []
        ren_open_tgt = client.request("textDocument/rename", {
            "textDocument": {"uri": m2_uri},
            "position": {"line": 0, "character": 8},
            "newName": "fetchA",
        })
        assert "error" in ren_open_tgt and ren_open_tgt["error"]["code"] == -32602, f"expected -32602 on open m2 conflict: {ren_open_tgt}"

        # (e) `use m2.load` + `open extra` (exporting `fetchA`) in same scope -> rejected (-32602)
        ms_open_extra_src = (
            "pub mod inner {\n"
            "    use m2.load\n"
            "    open extra\n"
            "    pub def run(): Int = load() + fetchA()\n"
            "}\n"
        )
        client.notifications.clear()
        client.notify("textDocument/didChange", {"textDocument": {"uri": ms_user_uri, "version": 5}, "contentChanges": [{"text": ms_open_extra_src}]})
        assert client.wait_diag_for(ms_user_uri) == []
        ren_open_ext = client.request("textDocument/rename", {
            "textDocument": {"uri": m2_uri},
            "position": {"line": 0, "character": 8},
            "newName": "fetchA",
        })
        assert "error" in ren_open_ext and ren_open_ext["error"]["code"] == -32602, f"expected -32602 on open extra conflict: {ren_open_ext}"

        # (f) Re-exported conflict via `bridge.gsa` (`pub use extra.fetchA`): `use m2.load; open bridge` -> rejected (-32602)
        bridge_ext_path = ms_dir / "bridge_ext.gsa"
        bridge_ext_path.write_text("pub use extra.fetchA\n", encoding="utf-8")
        ms_reexp_ext_src = (
            "pub mod inner {\n"
            "    use m2.load\n"
            "    open bridge_ext\n"
            "    pub def run(): Int = load() + fetchA()\n"
            "}\n"
        )
        client.notifications.clear()
        client.notify("textDocument/didChange", {"textDocument": {"uri": ms_user_uri, "version": 6}, "contentChanges": [{"text": ms_reexp_ext_src}]})
        assert client.wait_diag_for(ms_user_uri) == []
        ren_reexp_ext = client.request("textDocument/rename", {
            "textDocument": {"uri": m2_uri},
            "position": {"line": 0, "character": 8},
            "newName": "fetchA",
        })
        assert "error" in ren_reexp_ext and ren_reexp_ext["error"]["code"] == -32602, f"expected -32602 on re-exported open bridge_ext conflict: {ren_reexp_ext}"

        # (g) Re-exported target via `bridge_tgt.gsa` (`pub use m2.load`): `open bridge_tgt; def fetchA() = 93` -> rejected (-32602)
        bridge_tgt_path = ms_dir / "bridge_tgt.gsa"
        bridge_tgt_path.write_text("pub use m2.load\n", encoding="utf-8")
        ms_reexp_tgt_src = (
            "pub mod inner {\n"
            "    open bridge_tgt\n"
            "    def fetchA(): Int = 93\n"
            "    pub def run(): Int = load() + fetchA()\n"
            "}\n"
        )
        client.notifications.clear()
        client.notify("textDocument/didChange", {"textDocument": {"uri": ms_user_uri, "version": 7}, "contentChanges": [{"text": ms_reexp_tgt_src}]})
        assert client.wait_diag_for(ms_user_uri) == []
        ren_reexp_tgt = client.request("textDocument/rename", {
            "textDocument": {"uri": m2_uri},
            "position": {"line": 0, "character": 8},
            "newName": "fetchA",
        })
        assert "error" in ren_reexp_tgt and ren_reexp_tgt["error"]["code"] == -32602, f"expected -32602 on re-exported open bridge_tgt conflict: {ren_reexp_tgt}"

        # Helper to compile & run a renamed multi-file project with `geisha run`
        run_env = os.environ.copy()
        if "GEISHA_RUNTIME" in run_env and run_env["GEISHA_RUNTIME"]:
            run_env["GEISHA_RUNTIME"] = os.path.abspath(run_env["GEISHA_RUNTIME"])
        abs_geisha_bin = os.path.abspath(geisha_bin)

        # (h) Unaliased re-export propagation: `bridge_tgt.gsa` (`pub use m2.load`) + `use bridge_tgt.load` -> rename to `freshName` updates m2, bridge_tgt, AND `use bridge_tgt.load`, compiles & runs -> `7`
        bridge_tgt_uri = path_to_uri(bridge_tgt_path)
        ms_use_reexp_src = (
            "use std.str.intToStr\n"
            "use bridge_tgt.load\n"
            "def main(): Void = printLn(intToStr(load()))\n"
        )
        client.notifications.clear()
        client.notify("textDocument/didOpen", {"textDocument": {"uri": bridge_tgt_uri, "languageId": "geisha", "version": 1, "text": "pub use m2.load\n"}})
        assert client.wait_diag_for(bridge_tgt_uri) == []
        client.notify("textDocument/didChange", {"textDocument": {"uri": ms_user_uri, "version": 8}, "contentChanges": [{"text": ms_use_reexp_src}]})
        assert client.wait_diag_for(ms_user_uri) == []
        ren_prop = client.request("textDocument/rename", {
            "textDocument": {"uri": m2_uri},
            "position": {"line": 0, "character": 8},
            "newName": "freshName",
        })
        assert "result" in ren_prop, f"expected unaliased re-export rename to succeed: {ren_prop}"
        ch_prop = ren_prop["result"]["changes"]
        new_m2_prop = apply_edits(m2_src, ch_prop[m2_uri])
        new_bt_prop = apply_edits("pub use m2.load\n", ch_prop[bridge_tgt_uri])
        new_usr_prop = apply_edits(ms_use_reexp_src, ch_prop[ms_user_uri])
        assert new_bt_prop == "pub use m2.freshName\n", f"unexpected bridge_tgt: {new_bt_prop!r}"
        assert new_usr_prop == "use std.str.intToStr\nuse bridge_tgt.freshName\ndef main(): Void = printLn(intToStr(freshName()))\n", f"expected `use bridge_tgt.load` updated too, got: {new_usr_prop!r}"
        run_h_dir = root / "run_reexp_prop"
        run_h_dir.mkdir(parents=True)
        (run_h_dir / "m2.gsa").write_text(new_m2_prop, encoding="utf-8")
        (run_h_dir / "bridge_tgt.gsa").write_text(new_bt_prop, encoding="utf-8")
        (run_h_dir / "user.gsa").write_text(new_usr_prop, encoding="utf-8")
        res_h = subprocess.run(
            [abs_geisha_bin, "run", str(run_h_dir / "user.gsa")],
            cwd=str(run_h_dir),
            env=run_env,
            capture_output=True,
            text=True,
            timeout=60,
        )
        assert res_h.returncode == 0 and res_h.stdout.strip() == "7", f"renamed unaliased re-export failed to run: rc={res_h.returncode} stdout={res_h.stdout!r} stderr={res_h.stderr!r}"

        # (i) Aliased re-export stops propagation: `bridge_api.gsa` (`pub use m2.load as api`) + `use bridge_api.api; def fetchA() = 93` -> rename `m2.load` -> `fetchA` SUCCEEDS without false conflict, compiles & runs -> `100`
        bridge_api_path = ms_dir / "bridge_api.gsa"
        bridge_api_src = "pub use m2.load as api\n"
        bridge_api_path.write_text(bridge_api_src, encoding="utf-8")
        bridge_api_uri = path_to_uri(bridge_api_path)
        ms_use_api_src = (
            "use std.str.intToStr\n"
            "use bridge_api.api\n"
            "def fetchA(): Int = 93\n"
            "def main(): Void = printLn(intToStr(api() + fetchA()))\n"
        )
        client.notifications.clear()
        client.notify("textDocument/didOpen", {"textDocument": {"uri": bridge_api_uri, "languageId": "geisha", "version": 1, "text": bridge_api_src}})
        assert client.wait_diag_for(bridge_api_uri) == []
        client.notifications.clear()
        client.notify("textDocument/didChange", {"textDocument": {"uri": ms_user_uri, "version": 9}, "contentChanges": [{"text": ms_use_api_src}]})
        assert client.wait_diag_for(ms_user_uri) == []
        client.notify("textDocument/didClose", {"textDocument": {"uri": bridge_tgt_uri}})
        _ = client.wait_diag_for(bridge_tgt_uri)
        bridge_tgt_path.unlink()
        ren_api = client.request("textDocument/rename", {
            "textDocument": {"uri": m2_uri},
            "position": {"line": 0, "character": 8},
            "newName": "fetchA",
        })
        assert "result" in ren_api, f"expected aliased re-export rename to succeed without false conflict: {ren_api}"
        ch_api = ren_api["result"]["changes"]
        assert ms_user_uri not in ch_api, f"downstream `use bridge_api.api` must not be modified: {ch_api}"
        new_m2_api = apply_edits(m2_src, ch_api[m2_uri])
        new_bapi = apply_edits(bridge_api_src, ch_api[bridge_api_uri])
        assert new_m2_api == "pub def fetchA(): Int = 7\n" and new_bapi == "pub use m2.fetchA as api\n", f"unexpected edits: {new_m2_api!r}, {new_bapi!r}"
        client.notifications.clear()
        client.notify("textDocument/didChange", {"textDocument": {"uri": m2_uri, "version": 2}, "contentChanges": [{"text": new_m2_api}]})
        assert client.wait_diag_for(m2_uri) == []
        client.notify("textDocument/didChange", {"textDocument": {"uri": bridge_api_uri, "version": 2}, "contentChanges": [{"text": new_bapi}]})
        assert client.wait_diag_for(bridge_api_uri) == []
        assert client.wait_diag_for(ms_user_uri) == []
        run_i_dir = root / "run_reexp_api"
        run_i_dir.mkdir(parents=True)
        (run_i_dir / "m2.gsa").write_text(new_m2_api, encoding="utf-8")
        (run_i_dir / "bridge_api.gsa").write_text(new_bapi, encoding="utf-8")
        (run_i_dir / "user.gsa").write_text(ms_use_api_src, encoding="utf-8")
        res_i = subprocess.run(
            [abs_geisha_bin, "run", str(run_i_dir / "user.gsa")],
            cwd=str(run_i_dir),
            env=run_env,
            capture_output=True,
            text=True,
            timeout=60,
        )
        assert res_i.returncode == 0 and res_i.stdout.strip() == "100", f"renamed aliased re-export failed to run: rc={res_i.returncode} stdout={res_i.stdout!r} stderr={res_i.stderr!r}"

        # (j) Same-spelling explicit alias stops propagation: `bridge_same.gsa` (`pub use m2.load as load`) + `use bridge_same.load`
        same_dir = root / "same_alias_proj"
        same_dir.mkdir(parents=True)
        sa_m2_path = same_dir / "m2.gsa"
        sa_br_path = same_dir / "bridge_same.gsa"
        sa_usr_path = same_dir / "user.gsa"
        sa_m2_src = "pub def load(): Int = 7\n"
        sa_br_src = "pub use m2.load as load\n"
        sa_usr_src = (
            "use std.str.intToStr\n"
            "use bridge_same.load\n"
            "def main(): Void = printLn(intToStr(load()))\n"
        )
        sa_m2_path.write_text(sa_m2_src, encoding="utf-8")
        sa_br_path.write_text(sa_br_src, encoding="utf-8")
        sa_usr_path.write_text(sa_usr_src, encoding="utf-8")
        sa_m2_uri = path_to_uri(sa_m2_path)
        sa_br_uri = path_to_uri(sa_br_path)
        sa_usr_uri = path_to_uri(sa_usr_path)
        client.notifications.clear()
        for u, t in ((sa_m2_uri, sa_m2_src), (sa_br_uri, sa_br_src), (sa_usr_uri, sa_usr_src)):
            client.notify("textDocument/didOpen", {"textDocument": {"uri": u, "languageId": "geisha", "version": 1, "text": t}})
            assert client.wait_diag_for(u) == []
        ren_same = client.request("textDocument/rename", {
            "textDocument": {"uri": sa_m2_uri},
            "position": {"line": 0, "character": 8},
            "newName": "freshName",
        })
        assert "result" in ren_same, f"expected same-spelling alias rename to succeed: {ren_same}"
        ch_same = ren_same["result"]["changes"]
        assert sa_usr_uri not in ch_same, f"downstream `use bridge_same.load` / `load()` must NOT be edited when bridge pins `as load`: {ch_same}"
        new_sa_m2 = apply_edits(sa_m2_src, ch_same[sa_m2_uri])
        new_sa_br = apply_edits(sa_br_src, ch_same[sa_br_uri])
        assert new_sa_m2 == "pub def freshName(): Int = 7\n" and new_sa_br == "pub use m2.freshName as load\n", f"unexpected same-alias edits: {new_sa_m2!r}, {new_sa_br!r}"
        run_j_dir = root / "run_same_alias"
        run_j_dir.mkdir(parents=True)
        (run_j_dir / "m2.gsa").write_text(new_sa_m2, encoding="utf-8")
        (run_j_dir / "bridge_same.gsa").write_text(new_sa_br, encoding="utf-8")
        (run_j_dir / "user.gsa").write_text(sa_usr_src, encoding="utf-8")
        res_j = subprocess.run(
            [abs_geisha_bin, "run", str(run_j_dir / "user.gsa")],
            cwd=str(run_j_dir),
            env=run_env,
            capture_output=True,
            text=True,
            timeout=60,
        )
        assert res_j.returncode == 0 and res_j.stdout.strip() == "7", f"renamed same-spelling alias failed to run: rc={res_j.returncode} stdout={res_j.stdout!r} stderr={res_j.stderr!r}"

        # (k) Two-hop explicit alias round-trip (`load -> api -> load`): `hop1` (`pub use m2.load as api`), `hop2` (`pub use hop1.api as load`), `user` (`use hop2.load`)
        hop_dir = root / "two_hop_alias_proj"
        hop_dir.mkdir(parents=True)
        h_m2_path = hop_dir / "m2.gsa"
        h_1_path = hop_dir / "hop1.gsa"
        h_2_path = hop_dir / "hop2.gsa"
        h_usr_path = hop_dir / "user.gsa"
        h_m2_src = "pub def load(): Int = 7\n"
        h_1_src = "pub use m2.load as api\n"
        h_2_src = "pub use hop1.api as load\n"
        h_usr_src = (
            "use std.str.intToStr\n"
            "use hop2.load\n"
            "def main(): Void = printLn(intToStr(load()))\n"
        )
        h_m2_path.write_text(h_m2_src, encoding="utf-8")
        h_1_path.write_text(h_1_src, encoding="utf-8")
        h_2_path.write_text(h_2_src, encoding="utf-8")
        h_usr_path.write_text(h_usr_src, encoding="utf-8")
        h_m2_uri = path_to_uri(h_m2_path)
        h_1_uri = path_to_uri(h_1_path)
        h_2_uri = path_to_uri(h_2_path)
        h_usr_uri = path_to_uri(h_usr_path)
        client.notifications.clear()
        for u, t in ((h_m2_uri, h_m2_src), (h_1_uri, h_1_src), (h_2_uri, h_2_src), (h_usr_uri, h_usr_src)):
            client.notify("textDocument/didOpen", {"textDocument": {"uri": u, "languageId": "geisha", "version": 1, "text": t}})
            assert client.wait_diag_for(u) == []
        ren_hop = client.request("textDocument/rename", {
            "textDocument": {"uri": h_m2_uri},
            "position": {"line": 0, "character": 8},
            "newName": "freshName",
        })
        assert "result" in ren_hop, f"expected two-hop alias rename to succeed: {ren_hop}"
        ch_hop = ren_hop["result"]["changes"]
        assert h_2_uri not in ch_hop and h_usr_uri not in ch_hop, f"hop2/user must NOT be edited across explicit alias chain: {ch_hop}"
        new_h_m2 = apply_edits(h_m2_src, ch_hop[h_m2_uri])
        new_h_1 = apply_edits(h_1_src, ch_hop[h_1_uri])
        assert new_h_m2 == "pub def freshName(): Int = 7\n" and new_h_1 == "pub use m2.freshName as api\n", f"unexpected two-hop edits: {new_h_m2!r}, {new_h_1!r}"
        run_k_dir = root / "run_two_hop_alias"
        run_k_dir.mkdir(parents=True)
        (run_k_dir / "m2.gsa").write_text(new_h_m2, encoding="utf-8")
        (run_k_dir / "hop1.gsa").write_text(new_h_1, encoding="utf-8")
        (run_k_dir / "hop2.gsa").write_text(h_2_src, encoding="utf-8")
        (run_k_dir / "user.gsa").write_text(h_usr_src, encoding="utf-8")
        res_k = subprocess.run(
            [abs_geisha_bin, "run", str(run_k_dir / "user.gsa")],
            cwd=str(run_k_dir),
            env=run_env,
            capture_output=True,
            text=True,
            timeout=60,
        )
        assert res_k.returncode == 0 and res_k.stdout.strip() == "7", f"renamed two-hop alias failed to run: rc={res_k.returncode} stdout={res_k.stdout!r} stderr={res_k.stderr!r}"

        # (l) Qualified access with whitespace / comments between `.` and ident: `m2. load()`, `m2./*source*/load()`, `m2./*load*/load()`
        qws_dir = root / "qual_ws_proj"
        qws_dir.mkdir(parents=True)
        q_m2_path = qws_dir / "m2.gsa"
        q_usr_path = qws_dir / "user.gsa"
        q_m2_src = "pub def load(): Int = 7\n"
        q_usr_src = (
            "use std.str.intToStr\n"
            "use m2\n"
            "def main(): Void = printLn(intToStr(m2. load() + m2./*source*/load() + m2./*load*/load()))\n"
        )
        q_m2_path.write_text(q_m2_src, encoding="utf-8")
        q_usr_path.write_text(q_usr_src, encoding="utf-8")
        q_m2_uri = path_to_uri(q_m2_path)
        q_usr_uri = path_to_uri(q_usr_path)
        client.notifications.clear()
        for u, t in ((q_m2_uri, q_m2_src), (q_usr_uri, q_usr_src)):
            client.notify("textDocument/didOpen", {"textDocument": {"uri": u, "languageId": "geisha", "version": 1, "text": t}})
            assert client.wait_diag_for(u) == []
        ren_qws = client.request("textDocument/rename", {
            "textDocument": {"uri": q_m2_uri},
            "position": {"line": 0, "character": 8},
            "newName": "freshName",
        })
        assert "result" in ren_qws, f"expected qualified whitespace/comment rename to succeed: {ren_qws}"
        ch_qws = ren_qws["result"]["changes"]
        new_q_m2 = apply_edits(q_m2_src, ch_qws[q_m2_uri])
        new_q_usr = apply_edits(q_usr_src, ch_qws[q_usr_uri])
        assert "m2. freshName()" in new_q_usr and "m2./*source*/freshName()" in new_q_usr and "m2./*load*/freshName()" in new_q_usr, f"unexpected qualified rename: {new_q_usr!r}"
        run_l_dir = root / "run_qual_ws"
        run_l_dir.mkdir(parents=True)
        (run_l_dir / "m2.gsa").write_text(new_q_m2, encoding="utf-8")
        (run_l_dir / "user.gsa").write_text(new_q_usr, encoding="utf-8")
        res_l = subprocess.run(
            [abs_geisha_bin, "run", str(run_l_dir / "user.gsa")],
            cwd=str(run_l_dir),
            env=run_env,
            capture_output=True,
            text=True,
            timeout=60,
        )
        assert res_l.returncode == 0 and res_l.stdout.strip() == "21", f"renamed qualified ws/comment calls failed to run: rc={res_l.returncode} stdout={res_l.stdout!r} stderr={res_l.stderr!r}"

        # (m) Qualified type annotation `use a` + `def valOf(x: a.Marker): Int = x.val` -> rename `a.Marker` -> `NewMarker` rewrites `a.Marker` and runs -> `7`
        qt_dir = root / "qual_type_proj"
        qt_dir.mkdir(parents=True)
        qt_a_path = qt_dir / "a.gsa"
        qt_u_path = qt_dir / "user.gsa"
        qt_a_src = (
            "pub data Marker { MkMarker { val: Int } }\n"
            "pub def mk(): Marker = MkMarker { val: 7 }\n"
        )
        qt_u_src = (
            "use std.str.intToStr\n"
            "use a\n"
            "def valOf(x: a.Marker): Int = x.val\n"
            "def main(): Void = printLn(intToStr(valOf(a.mk())))\n"
        )
        qt_a_path.write_text(qt_a_src, encoding="utf-8")
        qt_u_path.write_text(qt_u_src, encoding="utf-8")
        qt_a_uri = path_to_uri(qt_a_path)
        qt_u_uri = path_to_uri(qt_u_path)
        client.notifications.clear()
        for u, t in ((qt_a_uri, qt_a_src), (qt_u_uri, qt_u_src)):
            client.notify("textDocument/didOpen", {"textDocument": {"uri": u, "languageId": "geisha", "version": 1, "text": t}})
            assert client.wait_diag_for(u) == []
        ren_qt = client.request("textDocument/rename", {
            "textDocument": {"uri": qt_a_uri},
            "position": {"line": 0, "character": 9},
            "newName": "NewMarker",
        })
        assert "result" in ren_qt, f"expected qualified type rename to succeed: {ren_qt}"
        ch_qt = ren_qt["result"]["changes"]
        new_qt_a = apply_edits(qt_a_src, ch_qt[qt_a_uri])
        new_qt_u = apply_edits(qt_u_src, ch_qt[qt_u_uri])
        assert "def valOf(x: a.NewMarker): Int = x.val" in new_qt_u, f"expected `a.Marker` rewritten to `a.NewMarker`, got: {new_qt_u!r}"
        run_m_dir = root / "run_qual_type"
        run_m_dir.mkdir(parents=True)
        (run_m_dir / "a.gsa").write_text(new_qt_a, encoding="utf-8")
        (run_m_dir / "user.gsa").write_text(new_qt_u, encoding="utf-8")
        res_m = subprocess.run(
            [abs_geisha_bin, "run", str(run_m_dir / "user.gsa")],
            cwd=str(run_m_dir),
            env=run_env,
            capture_output=True,
            text=True,
            timeout=60,
        )
        assert res_m.returncode == 0 and res_m.stdout.strip() == "7", f"renamed qualified type annotation failed to run: rc={res_m.returncode} stdout={res_m.stdout!r} stderr={res_m.stderr!r}"

        # (n) Qualified type paths with line comment + newline (`a.// source\nMarker`) and block comment containing target text (`a./* a.Marker */Marker`)
        qtc_dir = root / "qual_type_comment_proj"
        qtc_dir.mkdir(parents=True)
        qtc_a_path = qtc_dir / "a.gsa"
        qtc_u_path = qtc_dir / "user.gsa"
        qtc_a_src = (
            "pub data Marker { MkMarker { val: Int } }\n"
            "pub def mk(): Marker = MkMarker { val: 7 }\n"
        )
        qtc_u_src = (
            "use std.str.intToStr\n"
            "use a\n"
            "def valOf1(x: a.// source\n"
            "Marker): Int = x.val\n"
            "def valOf2(x: a./* a.Marker */Marker): Int = x.val\n"
            "def main(): Void = printLn(intToStr(valOf1(a.mk()) + valOf2(a.mk())))\n"
        )
        qtc_a_path.write_text(qtc_a_src, encoding="utf-8")
        qtc_u_path.write_text(qtc_u_src, encoding="utf-8")
        qtc_a_uri = path_to_uri(qtc_a_path)
        qtc_u_uri = path_to_uri(qtc_u_path)
        client.notifications.clear()
        for u, t in ((qtc_a_uri, qtc_a_src), (qtc_u_uri, qtc_u_src)):
            client.notify("textDocument/didOpen", {"textDocument": {"uri": u, "languageId": "geisha", "version": 1, "text": t}})
            assert client.wait_diag_for(u) == []
        ren_qtc = client.request("textDocument/rename", {
            "textDocument": {"uri": qtc_a_uri},
            "position": {"line": 0, "character": 9},
            "newName": "NewMarker",
        })
        assert "result" in ren_qtc, f"expected commented qualified type rename to succeed: {ren_qtc}"
        ch_qtc = ren_qtc["result"]["changes"]
        new_qtc_a = apply_edits(qtc_a_src, ch_qtc[qtc_a_uri])
        new_qtc_u = apply_edits(qtc_u_src, ch_qtc[qtc_u_uri])
        assert "a.// source\nNewMarker" in new_qtc_u and "a./* a.Marker */NewMarker" in new_qtc_u, f"unexpected commented qualified type rename: {new_qtc_u!r}"
        run_n_dir = root / "run_qual_type_comment"
        run_n_dir.mkdir(parents=True)
        (run_n_dir / "a.gsa").write_text(new_qtc_a, encoding="utf-8")
        (run_n_dir / "user.gsa").write_text(new_qtc_u, encoding="utf-8")
        res_n = subprocess.run(
            [abs_geisha_bin, "run", str(run_n_dir / "user.gsa")],
            cwd=str(run_n_dir),
            env=run_env,
            capture_output=True,
            text=True,
            timeout=60,
        )
        assert res_n.returncode == 0 and res_n.stdout.strip() == "14", f"renamed commented qualified type failed to run: rc={res_n.returncode} stdout={res_n.stdout!r} stderr={res_n.stderr!r}"

        # (o) Module and function share the same name: `use load` + `load.load()` -> rename `load.load` -> `freshName` updates ONLY second `load` and runs -> `7`
        samemod_dir = root / "same_mod_fn_proj"
        samemod_dir.mkdir(parents=True)
        sm_m_path = samemod_dir / "load.gsa"
        sm_u_path = samemod_dir / "user.gsa"
        sm_m_src = "pub def load(): Int = 7\n"
        sm_u_src = (
            "use std.str.intToStr\n"
            "use load\n"
            "def main(): Void = printLn(intToStr(load.load()))\n"
        )
        sm_m_path.write_text(sm_m_src, encoding="utf-8")
        sm_u_path.write_text(sm_u_src, encoding="utf-8")
        sm_m_uri = path_to_uri(sm_m_path)
        sm_u_uri = path_to_uri(sm_u_path)
        client.notifications.clear()
        for u, t in ((sm_m_uri, sm_m_src), (sm_u_uri, sm_u_src)):
            client.notify("textDocument/didOpen", {"textDocument": {"uri": u, "languageId": "geisha", "version": 1, "text": t}})
            assert client.wait_diag_for(u) == []
        ren_sm = client.request("textDocument/rename", {
            "textDocument": {"uri": sm_m_uri},
            "position": {"line": 0, "character": 8},
            "newName": "freshName",
        })
        assert "result" in ren_sm, f"expected same-name module/fn rename to succeed: {ren_sm}"
        ch_sm = ren_sm["result"]["changes"]
        new_sm_m = apply_edits(sm_m_src, ch_sm[sm_m_uri])
        new_sm_u = apply_edits(sm_u_src, ch_sm[sm_u_uri])
        assert new_sm_m == "pub def freshName(): Int = 7\n" and "load.freshName()" in new_sm_u and "use load\n" in new_sm_u, f"unexpected load.load() rename: {new_sm_m!r}, {new_sm_u!r}"
        run_o_dir = root / "run_same_mod_fn"
        run_o_dir.mkdir(parents=True)
        (run_o_dir / "load.gsa").write_text(new_sm_m, encoding="utf-8")
        (run_o_dir / "user.gsa").write_text(new_sm_u, encoding="utf-8")
        res_o = subprocess.run(
            [abs_geisha_bin, "run", str(run_o_dir / "user.gsa")],
            cwd=str(run_o_dir),
            env=run_env,
            capture_output=True,
            text=True,
            timeout=60,
        )
        assert res_o.returncode == 0 and res_o.stdout.strip() == "7", f"renamed load.load() failed to run: rc={res_o.returncode} stdout={res_o.stdout!r} stderr={res_o.stderr!r}"

        # (p) Value parameter name shares spelling with type name: `pub def number(Marker: Int): Int = Marker + 1` (untouched) & `pub def idMarker(Marker: Marker): Marker = Marker` (only type positions renamed)
        pt_dir = root / "param_vs_type_proj"
        pt_dir.mkdir(parents=True)
        pt_path = pt_dir / "main.gsa"
        pt_src = (
            "use std.str.intToStr\n"
            "pub data Marker { MkMarker { val: Int } }\n"
            "pub def number(Marker: Int): Int = Marker + 1\n"
            "pub def idMarker(Marker: Marker): Marker = Marker\n"
            "def main(): Void = printLn(intToStr(number(6) + idMarker(MkMarker { val: 10 }).val))\n"
        )
        pt_path.write_text(pt_src, encoding="utf-8")
        pt_uri = path_to_uri(pt_path)
        client.notifications.clear()
        client.notify("textDocument/didOpen", {"textDocument": {"uri": pt_uri, "languageId": "geisha", "version": 1, "text": pt_src}})
        assert client.wait_diag_for(pt_uri) == []
        ren_pt = client.request("textDocument/rename", {
            "textDocument": {"uri": pt_uri},
            "position": {"line": 1, "character": 9},
            "newName": "NewMarker",
        })
        assert "result" in ren_pt, f"expected param-vs-type rename to succeed: {ren_pt}"
        new_pt = apply_edits(pt_src, ren_pt["result"]["changes"][pt_uri])
        assert "pub data NewMarker { MkMarker { val: Int } }" in new_pt, f"expected data renamed: {new_pt!r}"
        assert "pub def number(Marker: Int): Int = Marker + 1" in new_pt, f"value parameter `Marker` in number() must NOT be renamed: {new_pt!r}"
        assert "pub def idMarker(Marker: NewMarker): NewMarker = Marker" in new_pt, f"only type annotations in idMarker() should be renamed: {new_pt!r}"
        run_p_dir = root / "run_param_vs_type"
        run_p_dir.mkdir(parents=True)
        (run_p_dir / "main.gsa").write_text(new_pt, encoding="utf-8")
        res_p = subprocess.run(
            [abs_geisha_bin, "run", str(run_p_dir / "main.gsa")],
            cwd=str(run_p_dir),
            env=run_env,
            capture_output=True,
            text=True,
            timeout=60,
        )
        assert res_p.returncode == 0 and res_p.stdout.strip() == "17", f"renamed param-vs-type program failed to run: rc={res_p.returncode} stdout={res_p.stdout!r} stderr={res_p.stderr!r}"

        # (q) Field rename in struct match pattern with comment & same-named binder: `Point { /* x */ x: x } -> x` -> `Point { /* x */ coord: x } -> x`, compiles & runs -> `7`
        fp_dir = root / "field_pat_proj"
        fp_dir.mkdir(parents=True)
        fp_path = fp_dir / "main.gsa"
        fp_src = (
            "use std.str.intToStr\n"
            "data Point { Point { x: Int, y: Int } }\n"
            "def getX(p: Point): Int = match p {\n"
            "    Point { /* x */ x: x } -> x,\n"
            "}\n"
            "def main(): Void = printLn(intToStr(getX(Point { x: 7, y: 2 })))\n"
        )
        fp_path.write_text(fp_src, encoding="utf-8")
        fp_uri = path_to_uri(fp_path)
        client.notifications.clear()
        client.notify("textDocument/didOpen", {"textDocument": {"uri": fp_uri, "languageId": "geisha", "version": 1, "text": fp_src}})
        assert client.wait_diag_for(fp_uri) == []
        ren_fp = client.request("textDocument/rename", {
            "textDocument": {"uri": fp_uri},
            "position": {"line": 1, "character": 21},
            "newName": "coord",
        })
        assert "result" in ren_fp, f"expected field pattern rename to succeed: {ren_fp}"
        new_fp = apply_edits(fp_src, ren_fp["result"]["changes"][fp_uri])
        assert "Point { /* x */ coord: x } -> x," in new_fp, f"comment and local binder `x` must be preserved verbatim, got: {new_fp!r}"
        assert "Point { coord: 7, y: 2 }" in new_fp, f"struct init field must be renamed: {new_fp!r}"
        run_q_dir = root / "run_field_pat"
        run_q_dir.mkdir(parents=True)
        (run_q_dir / "main.gsa").write_text(new_fp, encoding="utf-8")
        res_q = subprocess.run(
            [abs_geisha_bin, "run", str(run_q_dir / "main.gsa")],
            cwd=str(run_q_dir),
            env=run_env,
            capture_output=True,
            text=True,
            timeout=60,
        )
        assert res_q.returncode == 0 and res_q.stdout.strip() == "7", f"renamed field pattern program failed to run: rc={res_q.returncode} stdout={res_q.stdout!r} stderr={res_q.stderr!r}"

        # (r) Shorthand struct pattern field rename: `Point { x } -> x` expands to `Point { coord: x } -> x`, compiles & runs -> `7`
        sh_dir = root / "field_shorthand_proj"
        sh_dir.mkdir(parents=True)
        sh_path = sh_dir / "main.gsa"
        sh_src = (
            "use std.str.intToStr\n"
            "data Point { Point { x: Int, y: Int } }\n"
            "def getX(p: Point): Int = match p {\n"
            "    Point { x } -> x,\n"
            "}\n"
            "def main(): Void = printLn(intToStr(getX(Point { x: 7, y: 2 })))\n"
        )
        sh_path.write_text(sh_src, encoding="utf-8")
        sh_uri = path_to_uri(sh_path)
        client.notifications.clear()
        client.notify("textDocument/didOpen", {"textDocument": {"uri": sh_uri, "languageId": "geisha", "version": 1, "text": sh_src}})
        assert client.wait_diag_for(sh_uri) == []
        ren_sh = client.request("textDocument/rename", {
            "textDocument": {"uri": sh_uri},
            "position": {"line": 1, "character": 21},
            "newName": "coord",
        })
        assert "result" in ren_sh, f"expected shorthand field pattern rename to succeed: {ren_sh}"
        new_sh = apply_edits(sh_src, ren_sh["result"]["changes"][sh_uri])
        assert "Point { coord: x } -> x," in new_sh, f"shorthand `Point {{ x }}` must expand to `Point {{ coord: x }}`, got: {new_sh!r}"
        run_r_dir = root / "run_field_shorthand"
        run_r_dir.mkdir(parents=True)
        (run_r_dir / "main.gsa").write_text(new_sh, encoding="utf-8")
        res_r = subprocess.run(
            [abs_geisha_bin, "run", str(run_r_dir / "main.gsa")],
            cwd=str(run_r_dir),
            env=run_env,
            capture_output=True,
            text=True,
            timeout=60,
        )
        assert res_r.returncode == 0 and res_r.stdout.strip() == "7", f"renamed shorthand field pattern failed to run: rc={res_r.returncode} stdout={res_r.stdout!r} stderr={res_r.stderr!r}"

        # (s) Nested struct pattern with same-named field on a different type: `Both { p: Point { x: left }, q: Other { x: right } }` -> renames ONLY `Point.x`, leaves `Other.x` untouched, runs -> `10`
        nf_dir = root / "nested_field_pat_proj"
        nf_dir.mkdir(parents=True)
        nf_path = nf_dir / "main.gsa"
        nf_src = (
            "use std.str.intToStr\n"
            "data Point { Point { x: Int } }\n"
            "data Other { Other { x: Int } }\n"
            "data Both { Both { p: Point, q: Other } }\n"
            "def total(b: Both): Int = match b {\n"
            "    Both { p: Point { x: left }, q: Other { x: right } } -> left + right,\n"
            "}\n"
            "def main(): Void = printLn(intToStr(total(Both { p: Point { x: 7 }, q: Other { x: 3 } })))\n"
        )
        nf_path.write_text(nf_src, encoding="utf-8")
        nf_uri = path_to_uri(nf_path)
        client.notifications.clear()
        client.notify("textDocument/didOpen", {"textDocument": {"uri": nf_uri, "languageId": "geisha", "version": 1, "text": nf_src}})
        assert client.wait_diag_for(nf_uri) == []
        ren_nf = client.request("textDocument/rename", {
            "textDocument": {"uri": nf_uri},
            "position": {"line": 1, "character": 21},
            "newName": "coord",
        })
        assert "result" in ren_nf, f"expected nested struct pattern rename to succeed: {ren_nf}"
        new_nf = apply_edits(nf_src, ren_nf["result"]["changes"][nf_uri])
        assert "Both { p: Point { coord: left }, q: Other { x: right } } -> left + right," in new_nf, f"only Point.x should be renamed, Other.x untouched: {new_nf!r}"
        assert "Both { p: Point { coord: 7 }, q: Other { x: 3 } }" in new_nf, f"only Point init field should be renamed: {new_nf!r}"
        run_s_dir = root / "run_nested_field_pat"
        run_s_dir.mkdir(parents=True)
        (run_s_dir / "main.gsa").write_text(new_nf, encoding="utf-8")
        res_s = subprocess.run(
            [abs_geisha_bin, "run", str(run_s_dir / "main.gsa")],
            cwd=str(run_s_dir),
            env=run_env,
            capture_output=True,
            text=True,
            timeout=60,
        )
        assert res_s.returncode == 0 and res_s.stdout.strip() == "10", f"renamed nested field pattern failed to run: rc={res_s.returncode} stdout={res_s.stdout!r} stderr={res_s.stderr!r}"

        # (t) Parenthesized pattern `(Point { x }) -> x`, unit tuple `((), Point { x }) -> x`, and `let Point { x } = p; x` destructuring
        adv_dir = root / "adv_field_pat_proj"
        adv_dir.mkdir(parents=True)
        adv_path = adv_dir / "main.gsa"
        adv_src = (
            "use std.str.intToStr\n"
            "data Point { Point { x: Int } }\n"
            "def fParen(p: Point): Int = match p {\n"
            "    (Point { x }) -> x,\n"
            "}\n"
            "def fUnitTup(p: Point): Int = match ((), p) {\n"
            "    ((), Point { x }) -> x,\n"
            "}\n"
            "def fLet(p: Point): Int = {\n"
            "    let Point { x } = p;\n"
            "    x\n"
            "}\n"
            "def main(): Void = {\n"
            "    let p = Point { x: 7 };\n"
            "    printLn(intToStr(fParen(p) + fUnitTup(p) + fLet(p)))\n"
            "}\n"
        )
        adv_path.write_text(adv_src, encoding="utf-8")
        adv_uri = path_to_uri(adv_path)
        client.notifications.clear()
        client.notify("textDocument/didOpen", {"textDocument": {"uri": adv_uri, "languageId": "geisha", "version": 1, "text": adv_src}})
        assert client.wait_diag_for(adv_uri) == []
        ren_adv = client.request("textDocument/rename", {
            "textDocument": {"uri": adv_uri},
            "position": {"line": 1, "character": 21},
            "newName": "coord",
        })
        assert "result" in ren_adv, f"expected parenthesized/unit-tuple/let field rename to succeed: {ren_adv}"
        new_adv = apply_edits(adv_src, ren_adv["result"]["changes"][adv_uri])
        assert "(Point { coord: x }) -> x," in new_adv, f"parenthesized pattern mismatch: {new_adv!r}"
        assert "((), Point { coord: x }) -> x," in new_adv, f"unit tuple pattern mismatch: {new_adv!r}"
        assert "let Point { coord: x } = p;" in new_adv, f"let destructuring mismatch: {new_adv!r}"
        run_t_dir = root / "run_adv_field_pat"
        run_t_dir.mkdir(parents=True)
        (run_t_dir / "main.gsa").write_text(new_adv, encoding="utf-8")
        res_t = subprocess.run(
            [abs_geisha_bin, "run", str(run_t_dir / "main.gsa")],
            cwd=str(run_t_dir),
            env=run_env,
            capture_output=True,
            text=True,
            timeout=60,
        )
        assert res_t.returncode == 0 and res_t.stdout.strip() == "21", f"renamed paren/unit-tuple/let field patterns failed to run: rc={res_t.returncode} stdout={res_t.stdout!r} stderr={res_t.stderr!r}"

        # (u) Cursor-initiated rename inside patterns:
        #   (u1) cursor on `Other { x: right }` field label -> renames `Other.x`, leaves `Point.x` untouched, runs -> `10`
        #   (u2) cursor on `Point { x: x } -> x` LEFT of `:` -> renames `Point.x` field (NOT local `x`), runs -> `7`
        #   (u3) cursor on `Point { x: x } -> x` RIGHT of `:` -> renames local binder `x` (NOT field `Point.x`), runs -> `7`
        u1_line = "    Both { p: Point { x: left }, q: Other { x: right } } -> left + right,"
        other_x_col = u1_line.index("Other { x:") + len("Other { ")
        ren_u1 = client.request("textDocument/rename", {
            "textDocument": {"uri": nf_uri},
            "position": {"line": 5, "character": other_x_col},
            "newName": "otherCoord",
        })
        assert "result" in ren_u1, f"expected cursor-on-Other.x rename to succeed: {ren_u1}"
        new_u1 = apply_edits(nf_src, ren_u1["result"]["changes"][nf_uri])
        assert "data Point { Point { x: Int } }" in new_u1 and "data Other { Other { otherCoord: Int } }" in new_u1, f"expected ONLY Other.x renamed: {new_u1!r}"
        assert "Both { p: Point { x: left }, q: Other { otherCoord: right } } -> left + right," in new_u1, f"unexpected u1 pattern: {new_u1!r}"
        run_u1_dir = root / "run_cursor_other_x"
        run_u1_dir.mkdir(parents=True)
        (run_u1_dir / "main.gsa").write_text(new_u1, encoding="utf-8")
        res_u1 = subprocess.run([abs_geisha_bin, "run", str(run_u1_dir / "main.gsa")], cwd=str(run_u1_dir), env=run_env, capture_output=True, text=True, timeout=60)
        assert res_u1.returncode == 0 and res_u1.stdout.strip() == "10", f"u1 failed: rc={res_u1.returncode} stdout={res_u1.stdout!r} stderr={res_u1.stderr!r}"

        u23_dir = root / "cursor_pat_x_x_proj"
        u23_dir.mkdir(parents=True)
        u23_path = u23_dir / "main.gsa"
        u23_src = (
            "use std.str.intToStr\n"
            "data Point { Point { x: Int } }\n"
            "def getX(p: Point): Int = match p {\n"
            "    Point { x: x } -> x,\n"
            "}\n"
            "def main(): Void = printLn(intToStr(getX(Point { x: 7 })))\n"
        )
        u23_path.write_text(u23_src, encoding="utf-8")
        u23_uri = path_to_uri(u23_path)
        client.notifications.clear()
        client.notify("textDocument/didOpen", {"textDocument": {"uri": u23_uri, "languageId": "geisha", "version": 1, "text": u23_src}})
        assert client.wait_diag_for(u23_uri) == []
        pat_line = "    Point { x: x } -> x,"
        left_x_col = pat_line.index("x: x")
        right_x_col = pat_line.index(": x") + 2
        # (u2) cursor on field label `x` (left of `:`)
        ren_u2 = client.request("textDocument/rename", {
            "textDocument": {"uri": u23_uri},
            "position": {"line": 3, "character": left_x_col},
            "newName": "coord",
        })
        assert "result" in ren_u2, f"expected cursor-on-field-label rename to succeed: {ren_u2}"
        new_u2 = apply_edits(u23_src, ren_u2["result"]["changes"][u23_uri])
        assert "data Point { Point { coord: Int } }" in new_u2 and "Point { coord: x } -> x," in new_u2 and "Point { coord: 7 }" in new_u2, f"unexpected u2 edits: {new_u2!r}"
        run_u2_dir = root / "run_cursor_left_x"
        run_u2_dir.mkdir(parents=True)
        (run_u2_dir / "main.gsa").write_text(new_u2, encoding="utf-8")
        res_u2 = subprocess.run([abs_geisha_bin, "run", str(run_u2_dir / "main.gsa")], cwd=str(run_u2_dir), env=run_env, capture_output=True, text=True, timeout=60)
        assert res_u2.returncode == 0 and res_u2.stdout.strip() == "7", f"u2 failed: rc={res_u2.returncode} stdout={res_u2.stdout!r} stderr={res_u2.stderr!r}"
        # (u3) cursor on local binder `x` (right of `:`)
        ren_u3 = client.request("textDocument/rename", {
            "textDocument": {"uri": u23_uri},
            "position": {"line": 3, "character": right_x_col},
            "newName": "valX",
        })
        assert "result" in ren_u3, f"expected cursor-on-local-binder rename to succeed: {ren_u3}"
        new_u3 = apply_edits(u23_src, ren_u3["result"]["changes"][u23_uri])
        assert "data Point { Point { x: Int } }" in new_u3 and "Point { x: valX } -> valX," in new_u3 and "Point { x: 7 }" in new_u3, f"unexpected u3 edits: {new_u3!r}"
        run_u3_dir = root / "run_cursor_right_x"
        run_u3_dir.mkdir(parents=True)
        (run_u3_dir / "main.gsa").write_text(new_u3, encoding="utf-8")
        res_u3 = subprocess.run([abs_geisha_bin, "run", str(run_u3_dir / "main.gsa")], cwd=str(run_u3_dir), env=run_env, capture_output=True, text=True, timeout=60)
        assert res_u3.returncode == 0 and res_u3.stdout.strip() == "7", f"u3 failed: rc={res_u3.returncode} stdout={res_u3.stdout!r} stderr={res_u3.stderr!r}"

        # 12. shutdown -> requests return -32600; exit -> rc == 0
        shut = client.request("shutdown")
        assert shut["result"] is None
        post_shut = client.request("textDocument/hover", {
            "textDocument": {"uri": crlf_uri},
            "position": {"line": 0, "character": 4},
        })
        assert post_shut["error"]["code"] == -32600, f"expected -32600 after shutdown, got: {post_shut}"
        client.notify("exit")
        rc = client.proc.wait(timeout=10)
        assert rc == 0, f"expected exit code 0, got {rc}"

    print("PASS [geisha_lsp]: JSON-RPC stdio round-trip (diagnostics, hover, definition, references, prepareRename/rename, inlayHint, codeAction, documentSymbol, completion, UTF-8/CRLF, didClose, shutdown) verified!")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
