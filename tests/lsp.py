#!/usr/bin/env python3
"""Drive `jihoo lsp` as an editor would, over the Language Server Protocol."""

import argparse
import json
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]


class Client:
    def __init__(self, compiler, encodings):
        self.process = subprocess.Popen(
            [str(compiler), "lsp"], cwd=ROOT, stdin=subprocess.PIPE,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        self.next_id = 0
        self.notifications = []
        capabilities = {"general": {"positionEncodings": encodings}} if encodings else {}
        result = self.request("initialize", {"processId": None, "rootUri": None,
                                             "capabilities": capabilities})
        self.capabilities = result["capabilities"]
        assert result["serverInfo"]["name"] == "jihoo", result
        self.notify("initialized", {})

    def send(self, message):
        body = json.dumps(message).encode()
        self.process.stdin.write(b"Content-Length: %d\r\n\r\n" % len(body) + body)
        self.process.stdin.flush()

    def receive(self):
        length = None
        while True:
            line = self.process.stdout.readline()
            assert line, self.process.stderr.read()
            line = line.strip()
            if not line:
                break
            name, value = line.split(b":", 1)
            if name.lower() == b"content-length":
                length = int(value)
        return json.loads(self.process.stdout.read(length))

    def request(self, method, params):
        self.next_id += 1
        self.send({"jsonrpc": "2.0", "id": self.next_id, "method": method, "params": params})
        while True:
            message = self.receive()
            if message.get("id") == self.next_id and "method" not in message:
                assert "error" not in message, message
                return message["result"]
            self.notifications.append(message)

    def request_error(self, method, params):
        self.next_id += 1
        self.send({"jsonrpc": "2.0", "id": self.next_id, "method": method, "params": params})
        while True:
            message = self.receive()
            if message.get("id") == self.next_id:
                return message["error"]
            self.notifications.append(message)

    def notify(self, method, params):
        self.send({"jsonrpc": "2.0", "method": method, "params": params})

    def diagnostics(self, uri):
        """The next diagnostics published for `uri`."""
        while True:
            for i, message in enumerate(self.notifications):
                if (message.get("method") == "textDocument/publishDiagnostics"
                        and message["params"]["uri"] == uri):
                    del self.notifications[i]
                    return message["params"]["diagnostics"]
            self.notifications.append(self.receive())

    def close(self):
        assert self.request("shutdown", None) is None
        self.notify("exit", None)
        assert self.process.wait(timeout=30) == 0
        assert not self.process.stderr.read()


def uri(path):
    return path.resolve().as_uri()


def position(text, offset, utf8):
    before = text.encode()[:offset].decode()
    line = before.count("\n")
    column = before[before.rfind("\n") + 1:]
    units = len(column.encode()) if utf8 else len(column.encode("utf-16-le")) // 2
    return {"line": line, "character": units}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--compiler", type=Path, default=ROOT / "out/jihoo")
    compiler = parser.parse_args().compiler.resolve()

    with tempfile.TemporaryDirectory(prefix="jihoo-lsp-") as directory:
        directory = Path(directory)
        helper = directory / "helper.jh"
        helper.write_text("pub fn twice(x: i64) -> i64 { x * 2 }\n")
        main_file = directory / "main.jh"
        main_file.write_text("fn main() {}\n")
        source = ("import std.mem\nimport helper\n\n"
                  "struct Point {\n    x: i64\n}\n\n"
                  "fn main() {\n"
                  "    let s = \"가😀\"; let value = helper.twice(2)\n"
                  "    var v = Vec(String).new()\n"
                  "    let p = Point { x: value }\n"
                  "    let old = mem.replace(&v, Vec(String).new())\n"
                  "    println(value + p.x + old.len() + s.len + missing)\n"
                  "}\n")
        error_offset = source.encode().index(b"missing")

        for encodings, utf8 in [(["utf-8", "utf-16"], True), (None, False)]:
            client = Client(compiler, encodings)
            assert client.capabilities["positionEncoding"] == ("utf-8" if utf8 else "utf-16")
            assert client.capabilities["definitionProvider"] is True

            # Unsaved text is checked, not the file on disk.
            client.notify("textDocument/didOpen", {"textDocument": {
                "uri": uri(main_file), "languageId": "jihoo", "version": 1, "text": source}})
            diagnostics = client.diagnostics(uri(main_file))
            assert len(diagnostics) == 1, diagnostics
            diagnostic = diagnostics[0]
            assert "missing" in diagnostic["message"] and diagnostic["severity"] == 1, diagnostic
            assert diagnostic["range"]["start"] == position(source, error_offset, utf8), diagnostic
            assert diagnostic["range"]["end"] == position(source, error_offset + 7, utf8), diagnostic

            def definition(word, occurrence=0, after=0):
                offset = source.encode().index(word.encode(), after)
                for _ in range(occurrence):
                    offset = source.encode().index(word.encode(), offset + 1)
                return client.request("textDocument/definition", {
                    "textDocument": {"uri": uri(main_file)},
                    "position": position(source, offset + 1, utf8)})

            # A local, after a multibyte one on the same line.
            found = definition("value", 2)
            assert found["uri"] == uri(main_file), found
            assert found["range"]["start"] == position(source, source.encode().index(b"value"), utf8)
            # An item of an imported module, and the module itself.
            found = definition("twice")
            assert found["uri"] == uri(helper) and found["range"]["start"] == {"line": 0, "character": 7}
            found = definition("helper", 1)
            assert found["uri"] == uri(helper) and found["range"]["start"] == {"line": 0, "character": 0}
            # A struct, its field, and items of the standard library.
            found = definition("Point", 1)
            assert found["range"]["start"] == position(source, source.encode().index(b"Point"), utf8)
            found = definition("x", 0, source.encode().index(b"p.x"))
            assert found["range"]["start"] == position(source, source.encode().index(b"x: i64"), utf8)
            found = definition("replace")
            assert found["uri"] == uri(ROOT / "lib/std/mem.jh"), found
            found = definition("Vec")
            assert found["uri"] == uri(ROOT / "lib/std/vec.jh"), found

            # Fixing the error clears it.
            fixed = source.replace(" + missing", "")
            client.notify("textDocument/didChange", {"textDocument": {"uri": uri(main_file), "version": 2},
                                                     "contentChanges": [{"text": fixed}]})
            assert client.diagnostics(uri(main_file)) == []

            # A burst of edits that arrive together is checked once, with the last text.
            burst = b""
            for version in range(3, 8):
                text = fixed.replace("fn main() {", "fn main() {\n    let e%d = nope%d" % (version, version))
                body = json.dumps({"jsonrpc": "2.0", "method": "textDocument/didChange", "params": {
                    "textDocument": {"uri": uri(main_file), "version": version},
                    "contentChanges": [{"text": text}]}}).encode()
                burst += b"Content-Length: %d\r\n\r\n" % len(body) + body
            client.process.stdin.write(burst)
            client.process.stdin.flush()
            diagnostics = client.diagnostics(uri(main_file))
            assert [d["message"] for d in diagnostics] == ["unknown name `nope7`"], diagnostics

            # Formatting is one edit of the whole document.
            client.notify("textDocument/didChange", {"textDocument": {"uri": uri(main_file), "version": 9},
                                                     "contentChanges": [{"text": "fn main() {\n  let x=1\n}\n"}]})
            edits = client.request("textDocument/formatting", {"textDocument": {"uri": uri(main_file)},
                                                               "options": {"tabSize": 4, "insertSpaces": True}})
            assert edits == [{"range": {"start": {"line": 0, "character": 0},
                                        "end": {"line": 3, "character": 0}},
                              "newText": "fn main() {\n    let x = 1\n}\n"}], edits

            assert client.diagnostics(uri(main_file)) == []

            # An error inside a generic instance is shown at the use in the document.
            generic = (ROOT / "tests/fail/threads_instance_note.jh").read_text()
            client.notify("textDocument/didChange", {"textDocument": {"uri": uri(main_file), "version": 10},
                                                     "contentChanges": [{"text": generic}]})
            diagnostics = client.diagnostics(uri(main_file))
            assert len(diagnostics) == 1, diagnostics
            diagnostic = diagnostics[0]
            assert diagnostic["range"]["start"] == {"line": 8, "character": 4}, diagnostic
            assert "each_mut" in diagnostic["message"], diagnostic
            related = diagnostic["relatedInformation"]
            assert related[0]["location"]["uri"] == uri(ROOT / "lib/std/thread.jh"), related
            assert "in the instance" in related[1]["message"], related

            error = client.request_error("textDocument/hover", {
                "textDocument": {"uri": uri(main_file)}, "position": {"line": 0, "character": 0}})
            assert error["code"] == -32601, error

            # Closing clears what the document published.
            client.notify("textDocument/didClose", {"textDocument": {"uri": uri(main_file)}})
            assert client.diagnostics(uri(main_file)) == []
            client.close()

        # Requests before initialization fail; exit without shutdown is status 1.
        process = subprocess.Popen([str(compiler), "lsp"], stdin=subprocess.PIPE,
                                   stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        body = json.dumps({"jsonrpc": "2.0", "id": 1, "method": "shutdown"}).encode()
        exit_body = json.dumps({"jsonrpc": "2.0", "method": "exit"}).encode()
        output, errors = process.communicate(
            b"Content-Length: %d\r\n\r\n%s" % (len(body), body) +
            b"Content-Length: %d\r\n\r\n%s" % (len(exit_body), exit_body), timeout=30)
        assert process.returncode == 1 and not errors, errors
        assert b'"code":-32002' in output, output

        result = subprocess.run([str(compiler), "lsp", "main.jh"], capture_output=True)
        assert result.returncode == 2 and b"lsp takes no files" in result.stderr

    print("Language server: diagnostics, definitions, formatting and lifecycle passed")


if __name__ == "__main__":
    main()
