"""The editor path: drive `lake serve` as an LSP client would.

What it pins: in async mode the job's result reaches the editor WITHOUT an
edit (the watcher is a snapshot task, so the server publishes its
diagnostics when it finishes), the rest of the file stays answered while the
job runs, and the lightbulb offers the result once it is in.

Run from the repository root after `lake build`:
    python3 -m unittest tests.test_server -v
"""
import json
import os
import shutil
import subprocess
import threading
import time
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SCRATCH = ROOT / ".vibe-test-server"
STATE = SCRATCH / "state"

SOURCE = """import Vibe
set_option vibe.mode "async"
set_option vibe.llm "python3 tests/fake_llm.py"

def sumTo (n : Nat) : {s : Nat // 2 * s = n * (n + 1)} := by
  vibe

theorem after_it : 1 + 1 = 2 := rfl
"""

SCRIPT = """exact match n with
| 0 => ⟨0, rfl⟩
| k + 1 => ⟨(sumTo k).val + (k + 1), by
    have := (sumTo k).property
    simp [Nat.mul_add, Nat.add_mul] at *
    omega⟩"""


class Lsp:
    def __init__(self, env):
        self.p = subprocess.Popen(["lake", "serve"], cwd=ROOT, env=env, stdin=subprocess.PIPE,
                                  stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
        self.next_id = 0
        self.responses = {}
        self.notes = []          # (time, method, params)
        self.cv = threading.Condition()
        threading.Thread(target=self._read, daemon=True).start()

    def _read(self):
        f = self.p.stdout
        while True:
            line = f.readline()
            if not line:
                return
            if not line.startswith(b"Content-Length"):
                continue
            n = int(line.split(b":")[1])
            while f.readline().strip():
                pass
            msg = json.loads(f.read(n))
            with self.cv:
                if "id" in msg and "method" not in msg:
                    self.responses[msg["id"]] = (time.time(), msg)
                elif "id" in msg:  # server request: answer null
                    self.send({"jsonrpc": "2.0", "id": msg["id"], "result": None})
                else:
                    self.notes.append((time.time(), msg["method"], msg.get("params")))
                self.cv.notify_all()

    def send(self, msg):
        body = json.dumps(msg).encode()
        self.p.stdin.write(b"Content-Length: %d\r\n\r\n" % len(body) + body)
        self.p.stdin.flush()

    def request(self, method, params, timeout=120):
        self.next_id += 1
        i = self.next_id
        t0 = time.time()
        self.send({"jsonrpc": "2.0", "id": i, "method": method, "params": params})
        with self.cv:
            if not self.cv.wait_for(lambda: i in self.responses, timeout):
                return None, timeout
        t, msg = self.responses[i]
        return msg, t - t0

    def notify(self, method, params):
        self.send({"jsonrpc": "2.0", "method": method, "params": params})

    def wait_diag(self, text, timeout):
        def found():
            for _, m, p in self.notes:
                if m == "textDocument/publishDiagnostics":
                    if any(text in d["message"] for d in p["diagnostics"]):
                        return True
            return False
        with self.cv:
            return self.cv.wait_for(found, timeout)

    def close(self):
        self.p.kill()


class ServerAsync(unittest.TestCase):
    CANDIDATE = {"kind": "solution", "script": SCRIPT}
    def setUp(self):
        shutil.rmtree(SCRATCH, ignore_errors=True)
        STATE.mkdir(parents=True)
        cand = SCRATCH / "cand.json"
        cand.write_text(json.dumps(self.CANDIDATE))
        self.file = SCRATCH / "T.lean"
        self.file.write_text(SOURCE)
        env = dict(os.environ, VIBE_DIR=str(STATE), FAKE_CANDIDATE=str(cand), FAKE_DELAY="20")
        self.lsp = Lsp(env)
        self.uri = self.file.as_uri()
        self.lsp.request("initialize", {"processId": None, "rootUri": ROOT.as_uri(),
                                        "capabilities": {}})
        self.lsp.notify("initialized", {})
        self.lsp.notify("textDocument/didOpen", {"textDocument": {
            "uri": self.uri, "languageId": "lean4", "version": 1, "text": SOURCE}})

    def tearDown(self):
        self.lsp.close()

    def code_actions(self, pos, timeout=60):
        r, dt = self.lsp.request("textDocument/codeAction", {
            "textDocument": {"uri": self.uri},
            "range": {"start": pos, "end": pos}, "context": {"diagnostics": []}}, timeout)
        return ((r or {}).get("result") or []), dt

    def test_result_arrives_without_an_edit(self):
        lsp = self.lsp
        self.assertTrue(lsp.wait_diag("started job", 300), "no 'started job' diagnostic")
        t_started = time.time()
        # While the job runs (the fake agent sleeps 20 s), the rest of the file
        # answers at once. (Requests INSIDE the declaration wait for the job:
        # Lean runs a command's linters after its whole snapshot tree, and the
        # command's info tree waits for the linters.)
        hover, dt = lsp.request("textDocument/hover", {"textDocument": {"uri": self.uri},
                                "position": {"line": 7, "character": 10}}, 60)
        self.assertIsNotNone(hover)
        self.assertLess(dt, 5, "a later declaration waited for the job")
        self.assertLess(time.time() - t_started, 15, "the job finished before we could look")
        # The result is published with NO didChange from us.
        self.assertTrue(lsp.wait_diag("job finished", 300), "result never published")
        print(f"\nresult published {time.time() - t_started:.1f}s after 'started job'")
        # The interactive form of the message matches a cache hit's (this client
        # declares no widget support, so both arrive with the `[apply]` fallback).
        sess, _ = lsp.request("$/lean/rpc/connect", {"uri": self.uri})
        diags, _ = lsp.request("$/lean/rpc/call", {
            "sessionId": sess["result"]["sessionId"],
            "method": "Lean.Widget.getInteractiveDiagnostics",
            "textDocument": {"uri": self.uri}, "position": {"line": 0, "character": 0},
            "params": {}})
        blob = json.dumps(diags, ensure_ascii=False)
        self.assertIn("job finished", blob)
        self.assertIn("[apply] exact match n with", blob)
        # The lightbulb: the provider reads the cache entry at the pending `vibe`.
        actions, dt = self.code_actions({"line": 5, "character": 3})
        vibe = [a for a in actions if a["title"].startswith("vibe:")]
        self.assertEqual(len(vibe), 1, actions)
        edit = vibe[0]["edit"]["documentChanges"][0]["edits"][0]
        self.assertEqual(edit["range"], {"start": {"line": 5, "character": 2},
                                         "end": {"line": 5, "character": 6}})
        self.assertTrue(edit["newText"].startswith("exact match n with\n  | 0 =>"), edit)
        print(f"code action {dt:.1f}s: {vibe[0]['title']}")


HELPERS = ("def sumTo_impl : Nat → Nat\n| 0 => 0\n| k + 1 => sumTo_impl k + (k + 1)\n\n"
           "theorem sumTo_impl_spec (n : Nat) : 2 * sumTo_impl n = n * (n + 1) := by\n"
           "  induction n with\n  | zero => rfl\n"
           "  | succ k ih => simp [sumTo_impl, Nat.mul_add, Nat.add_mul] at *; omega")


class ServerAsyncHelpers(ServerAsync):
    CANDIDATE = {"kind": "solution", "helpers": HELPERS,
                 "script": "exact ⟨sumTo_impl n, sumTo_impl_spec n⟩"}

    def test_result_arrives_without_an_edit(self):
        self.assertTrue(self.lsp.wait_diag("started job", 300))
        self.assertTrue(self.lsp.wait_diag("job finished", 300), "result never published")
        actions, _ = self.code_actions({"line": 5, "character": 3})
        vibe = [a for a in actions if a["title"].startswith("vibe:")]
        self.assertEqual(len(vibe), 1, actions)
        edit = vibe[0]["edit"]["documentChanges"][0]["edits"][0]
        # the span starts at the declaration, so the helpers land above it
        self.assertEqual(edit["range"]["start"], {"line": 4, "character": 0})
        self.assertTrue(edit["newText"].startswith("def sumTo_impl"), edit)
        self.assertIn("\n\ndef sumTo (n : Nat)", edit["newText"])
        self.assertTrue(edit["newText"].endswith("exact ⟨sumTo_impl n, sumTo_impl_spec n⟩"))


if __name__ == "__main__":
    unittest.main()
