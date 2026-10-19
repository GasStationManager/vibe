"""End-to-end tests of the tactic + agent + checker with a fake LLM.

Run from the repository root after `lake build`:
    python3 -m unittest discover -s tests -v
"""
import json
import os
import shutil
import subprocess
import time
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SCRATCH = ROOT / ".vibe-test"
STATE = SCRATCH / "state"

HEADER = """import Vibe
set_option vibe.mode "sync"
set_option vibe.llm "python3 tests/fake_llm.py"
"""

SUM_SPEC = "def sumTo (n : Nat) : {s : Nat // 2 * s = n * (n + 1)} := by\n  vibe\n"

SUM_SCRIPT = """exact match n with
| 0 => ⟨0, rfl⟩
| k + 1 => ⟨(sumTo k).val + (k + 1), by
    have := (sumTo k).property
    simp [Nat.mul_add, Nat.add_mul] at *
    omega⟩"""


class Pipeline(unittest.TestCase):
    def setUp(self):
        shutil.rmtree(SCRATCH, ignore_errors=True)
        SCRATCH.mkdir()
        STATE.mkdir()

    def lean(self, body, *cands, header=HEADER, env=None):
        paths = []
        for i, c in enumerate(cands):
            p = SCRATCH / f"cand{i}.json"
            p.write_text(json.dumps(c))
            paths.append(str(p))
        f = SCRATCH / "T.lean"
        f.write_text(header + "\n" + body)
        e = dict(os.environ, FAKE_CANDIDATE=":".join(paths), VIBE_DIR=str(STATE))
        e.update(env or {})
        r = subprocess.run(["lake", "env", "lean", str(f)], cwd=ROOT, capture_output=True,
                           text=True, env=e, timeout=900)
        return r.returncode, r.stdout + r.stderr

    def cache(self):
        return [json.loads(p.read_text()) for p in (STATE / "cache").glob("*.json")
                if not p.name.endswith(".stale.json")]

    def test_solution_checked_and_suggested(self):
        rc, out = self.lean(SUM_SPEC, {"kind": "solution", "script": SUM_SCRIPT})
        self.assertEqual(rc, 0, out)
        self.assertIn("vibe: checked. Try this:", out)
        self.assertIn("(sumTo k).val + (k + 1)", out)
        # a second elaboration is a cache hit: no agent (FAKE_CANDIDATE unset would fail)
        rc, out = self.lean(SUM_SPEC, env={"FAKE_CANDIDATE": "/nonexistent"})
        self.assertEqual(rc, 0, out)
        self.assertIn("vibe: checked", out)

    def test_wrong_then_right(self):
        wrong = {"kind": "solution", "script": "exact ⟨n, by omega⟩"}
        rc, out = self.lean(SUM_SPEC, wrong, {"kind": "solution", "script": SUM_SCRIPT})
        self.assertEqual(rc, 0, out)
        log = next((STATE / "work").glob("*/agent.log")).read_text()
        self.assertIn("compile errors", log)
        prompt1 = next((STATE / "work").glob("*/prompt1.md")).read_text()
        self.assertIn("REJECTED", prompt1)

    def test_sorry_and_native_decide_refused(self):
        for script in ("exact ⟨0, sorry⟩", "exact ⟨n * (n + 1) / 2, by native_decide⟩"):
            shutil.rmtree(STATE, ignore_errors=True); STATE.mkdir()
            rc, out = self.lean(SUM_SPEC, {"kind": "solution", "script": script})
            self.assertNotEqual(rc, 0, out)
            self.assertIn("banned tokens", out)

    def test_helpers_suggest_whole_span(self):
        helpers = ("def sumTo_impl : Nat → Nat\n| 0 => 0\n| k + 1 => sumTo_impl k + (k + 1)\n\n"
                   "theorem sumTo_impl_spec (n : Nat) : 2 * sumTo_impl n = n * (n + 1) := by\n"
                   "  induction n with\n  | zero => rfl\n"
                   "  | succ k ih => simp [sumTo_impl, Nat.mul_add, Nat.add_mul] at *; omega")
        rc, out = self.lean(SUM_SPEC, {"kind": "solution", "helpers": helpers,
                                       "script": "exact ⟨sumTo_impl n, sumTo_impl_spec n⟩"})
        self.assertEqual(rc, 0, out)
        self.assertIn("adds helper declarations above", out)
        self.assertIn("def sumTo_impl", out)
        self.assertIn("def sumTo (n : Nat)", out)  # the span includes the declaration head

    def test_helper_cannot_change_the_spec(self):
        spec = ("def target (n : Nat) : Nat := n + 1\n\n"
                "def f (n : Nat) : {m : Nat // m = target n} := by\n  vibe\n")
        # A notation inserted above `f` re-parses its statement as `m = 0`.
        sneaky = {"kind": "solution",
                  "helpers": 'local notation "target" n => (0 : Nat)',
                  "script": "exact ⟨0, rfl⟩"}
        rc, out = self.lean(spec, sneaky)
        self.assertNotEqual(rc, 0, out)
        log = next((STATE / "work").glob("*/agent.log")).read_text()
        self.assertIn("type changed", log)

    def test_spec_defect_certified(self):
        spec = "def g (n : Nat) : {m : Nat // m < 0} := by\n  vibe\n"
        cert = {"kind": "spec_defect", "defect": "unsat",
                "explanation": "no natural number is below 0",
                "certificate": "theorem g_unsat : ¬ ∃ m : Nat, m < 0 := by omega"}
        rc, out = self.lean(spec, cert)
        self.assertNotEqual(rc, 0)
        self.assertIn("SPEC DEFECT (unsat)", out)
        self.assertIn("theorem g_unsat", out)

    def test_bogus_certificate_refused(self):
        spec = "def g (n : Nat) : {m : Nat // m < n + 1} := by\n  vibe\n"
        cert = {"kind": "spec_defect", "defect": "unsat", "explanation": "lies",
                "certificate": "theorem g_unsat : ¬ ∃ m : Nat, m < 1 := by omega"}
        rc, out = self.lean(spec, cert)
        self.assertNotEqual(rc, 0)
        self.assertIn("gave up", out)

    def test_plan_with_vibe_holes(self):
        spec = ("def twice (n : Nat) : {m : Nat // m = 2 * n} := by\n  vibe\n")
        plan = {"kind": "solution",
                "helpers": "def twice_dbl (n : Nat) : {m : Nat // m = n + n} := by\n  vibe",
                "script": "exact ⟨(twice_dbl n).val, by have := (twice_dbl n).property; omega⟩"}
        rc, out = self.lean(spec, plan)
        self.assertEqual(rc, 0, out)
        self.assertIn("adds helper declarations above", out)
        entry = self.cache()[0]
        self.assertEqual(entry["holes"], 1)
        self.assertIn("sorryAx", entry["axioms"])

    def test_stale_cache_reasks(self):
        rc, out = self.lean(SUM_SPEC, {"kind": "solution", "script": SUM_SCRIPT})
        self.assertEqual(rc, 0, out)
        # Corrupt the cached script: it no longer checks, so the agent is asked again.
        p = next(p for p in (STATE / "cache").glob("*.json"))
        e = json.loads(p.read_text()); e["script"] = "exact ⟨0, rfl⟩"; p.write_text(json.dumps(e))
        rc, out = self.lean(SUM_SPEC, {"kind": "solution", "script": SUM_SCRIPT})
        self.assertEqual(rc, 0, out)
        self.assertIn("no longer checks", out)
        prompt = next((STATE / "work").glob("*/prompt0.md")).read_text()
        self.assertIn("no longer checks in the current file", prompt)

    def test_async_then_hit(self):
        header = HEADER.replace('"sync"', '"async"')
        rc, out = self.lean(SUM_SPEC, {"kind": "solution", "script": SUM_SCRIPT}, header=header)
        self.assertIn("started job", out)
        for _ in range(240):
            if self.cache():
                break
            time.sleep(1)
        rc, out = self.lean(SUM_SPEC, header=header, env={"FAKE_CANDIDATE": "/nonexistent"})
        self.assertEqual(rc, 0, out)
        self.assertIn("vibe: checked", out)

    def test_offline_never_starts(self):
        header = HEADER.replace('"sync"', '"offline"')
        rc, out = self.lean(SUM_SPEC, header=header)
        self.assertIn("no cached result", out)
        self.assertFalse((STATE / "jobs").exists() and any((STATE / "jobs").iterdir()))


if __name__ == "__main__":
    unittest.main()
