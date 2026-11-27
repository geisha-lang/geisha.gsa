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
    def __init__(self, geisha_bin: str, cwd: str) -> None:
        self.proc = subprocess.Popen(
            [geisha_bin, "lsp"],
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


def path_to_uri(p: Path) -> str:
    return p.resolve().as_uri()


def main() -> int:
    geisha_bin = sys.argv[1] if len(sys.argv) > 1 else os.environ.get("GEISHA_BIN", "build/geisha2")
    geisha_bin = str(Path(geisha_bin).resolve())

    with tempfile.TemporaryDirectory(prefix="geisha_lsp_test_") as td:
        root = Path(td)
        helper_path = root / "helper.gsa"
        helper_src = (
            "/// Multiply an integer by two.\n"
            "pub def doubleVal(n: Int): Int = n * 2\n"
        )
        helper_path.write_text(helper_src, encoding="utf-8")

        main_path = root / "main.gsa"
        main_src = (
            "use std.str.{intToStr}\n"
            "use helper.{doubleVal}\n"
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
            "def main(): Void = {\n"
            "    let total = addNums(10, doubleVal(16));\n"
            "    printLn(intToStr(total))\n"
            "}\n"
        )
        main_path.write_text(main_src, encoding="utf-8")

        main_uri = path_to_uri(main_path)
        helper_uri = path_to_uri(helper_path)

        client = LspClient(geisha_bin, str(root))

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

        # 3. documentSymbol
        sym_resp = client.request("textDocument/documentSymbol", {
            "textDocument": {"uri": main_uri},
        })
        syms = sym_resp["result"]
        sym_names = [s["name"] for s in syms]
        for expected in ("Point", "Shape", "Describable", "addNums", "main"):
            assert expected in sym_names, f"missing symbol {expected!r} in {sym_names}"
        shape_sym = next(s for s in syms if s["name"] == "Shape")
        variant_names = [c["name"] for c in shape_sym.get("children", [])]
        assert "Circle" in variant_names and "Rect" in variant_names, f"missing Shape variants: {variant_names}"
        desc_sym = next(s for s in syms if s["name"] == "Describable")
        method_names = [c["name"] for c in desc_sym.get("children", [])]
        assert "describe" in method_names, f"missing concept method: {method_names}"

        # 4. hover on `addNums` call (line 19, col 18) -> inferred type + `///` doc
        hover_add = client.request("textDocument/hover", {
            "textDocument": {"uri": main_uri},
            "position": {"line": 19, "character": 18},
        })
        assert hover_add["result"] is not None, f"hover on addNums returned null"
        hover_add_md = hover_add["result"]["contents"]["value"]
        assert "Int" in hover_add_md, f"expected Int in hover: {hover_add_md}"
        assert "Add two integers together." in hover_add_md, f"expected doc comment in hover: {hover_add_md}"

        # 4b. hover on `doubleVal` call (line 19, col 31) -> cross-file inferred type + `///` doc
        hover_dbl = client.request("textDocument/hover", {
            "textDocument": {"uri": main_uri},
            "position": {"line": 19, "character": 31},
        })
        assert hover_dbl["result"] is not None, f"hover on doubleVal returned null"
        hover_dbl_md = hover_dbl["result"]["contents"]["value"]
        assert "Int" in hover_dbl_md and "Multiply an integer by two." in hover_dbl_md, f"unexpected hover: {hover_dbl_md}"

        # 4c. hover on `total` in `intToStr(total)` (line 20, col 22) -> inferred `Int`
        hover_tot = client.request("textDocument/hover", {
            "textDocument": {"uri": main_uri},
            "position": {"line": 20, "character": 22},
        })
        assert hover_tot["result"] is not None, "hover on total returned null"
        assert "Int" in hover_tot["result"]["contents"]["value"], f"unexpected hover on total: {hover_tot}"

        # 5. definition on `addNums` (same file) and `doubleVal` (cross-file helper.gsa)
        def_add = client.request("textDocument/definition", {
            "textDocument": {"uri": main_uri},
            "position": {"line": 19, "character": 18},
        })
        assert def_add["result"] is not None, "definition for addNums returned null"
        assert def_add["result"]["uri"] == main_uri
        assert def_add["result"]["range"]["start"]["line"] == 16, f"unexpected addNums def line: {def_add}"

        def_dbl = client.request("textDocument/definition", {
            "textDocument": {"uri": main_uri},
            "position": {"line": 19, "character": 31},
        })
        assert def_dbl["result"] is not None, "definition for doubleVal returned null"
        assert def_dbl["result"]["uri"] == helper_uri, f"expected {helper_uri}, got {def_dbl}"
        assert def_dbl["result"]["range"]["start"]["line"] == 1, f"unexpected doubleVal def line: {def_dbl}"

        # 6. completion: `std.`, `sys.`, `std.str.`, and local/imported identifiers
        comp_src = main_src + "\ndef _c1() = std.\ndef _c2() = sys.\ndef _c3() = std.str.\ndef _c4() = add\n"
        client.notify("textDocument/didChange", {
            "textDocument": {"uri": main_uri, "version": 2},
            "contentChanges": [{"text": comp_src}],
        })
        _ = client.wait_notification("textDocument/publishDiagnostics")

        comp_std = client.request("textDocument/completion", {
            "textDocument": {"uri": main_uri},
            "position": {"line": 23, "character": 16},
        })
        std_labels = {it["label"] for it in comp_std["result"]["items"]}
        assert {"str", "json", "list", "vec", "map", "option", "result"}.issubset(std_labels), f"missing std.* modules: {std_labels}"

        comp_sys = client.request("textDocument/completion", {
            "textDocument": {"uri": main_uri},
            "position": {"line": 24, "character": 16},
        })
        sys_labels = {it["label"] for it in comp_sys["result"]["items"]}
        assert {"io", "fs", "env", "proc"}.issubset(sys_labels), f"missing sys.* modules: {sys_labels}"

        comp_str = client.request("textDocument/completion", {
            "textDocument": {"uri": main_uri},
            "position": {"line": 25, "character": 20},
        })
        str_labels = {it["label"] for it in comp_str["result"]["items"]}
        assert {"intToStr", "strStartsWith", "strJoin"}.issubset(str_labels), f"missing std.str exports: {str_labels}"

        comp_local = client.request("textDocument/completion", {
            "textDocument": {"uri": main_uri},
            "position": {"line": 26, "character": 15},
        })
        local_labels = {it["label"] for it in comp_local["result"]["items"]}
        assert "addNums" in local_labels, f"missing local def addNums in completion: {local_labels}"

        # 7. didChange with type error -> publishDiagnostics with exact line & severity 1
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
        diag_err = client.wait_notification("textDocument/publishDiagnostics")
        diags = diag_err["params"]["diagnostics"]
        assert len(diags) == 1, f"expected 1 diagnostic, got: {diags}"
        d0 = diags[0]
        assert d0["severity"] == 1
        assert d0["source"] == "geisha"
        assert d0["range"]["start"]["line"] == 1, f"expected error on line 1, got: {d0}"
        assert "Int" in d0["message"] and "String" in d0["message"], f"unexpected error msg: {d0}"

        # 8. didChange back to valid -> clears diagnostics
        client.notify("textDocument/didChange", {
            "textDocument": {"uri": main_uri, "version": 4},
            "contentChanges": [{"text": main_src}],
        })
        diag_clear = client.wait_notification("textDocument/publishDiagnostics")
        assert diag_clear["params"]["diagnostics"] == []

        # 9. unknown method -> -32601
        unk = client.request("geisha/nonExistentMethod", {})
        assert unk["error"]["code"] == -32601, f"expected -32601, got: {unk}"

        # 10. didClose + shutdown + exit -> rc == 0
        client.notify("textDocument/didClose", {"textDocument": {"uri": main_uri}})
        _ = client.wait_notification("textDocument/publishDiagnostics")
        shut = client.request("shutdown")
        assert shut["result"] is None
        client.notify("exit")
        rc = client.proc.wait(timeout=10)
        assert rc == 0, f"expected exit code 0, got {rc}"

    print("PASS [geisha_lsp]: JSON-RPC stdio round-trip (diagnostics, hover, definition, documentSymbol, completion, shutdown) verified!")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
