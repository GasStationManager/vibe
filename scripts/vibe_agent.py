#!/usr/bin/env python3
"""The vibe agent: turns one `vibe` request into a CHECKED cache entry.

    vibe_agent.py run REQUEST.json [--llm CMD]   # called by the tactic
    vibe_agent.py check REQUEST.json CANDIDATE.json   # the checker (the agent calls it too)

`run` renders `prompts/vibe.md`, hands it to an LLM agent CLI on stdin
(default `claude -p --dangerously-skip-permissions`, override with `--llm`,
`set_option vibe.llm`, or `VIBE_LLM`), and expects the agent to write
`.vibe/work/<key>/candidate.json`. The candidate is then checked HERE, by
`check`, whatever the agent claims; only a passing candidate (or a checked
spec-defect certificate) becomes `.vibe/cache/<key>.json`. A failing one is
handed back to the agent with the checker's output, up to `VIBE_ROUNDS`
rounds (default 2), and after that the cache records a failure.

The checker compiles a copy of the file (`lake env lean`, `VIBE_MODE=offline`
so other `vibe` holes never start agents) with the candidate spliced in, cut
after the target declaration, and requires:
  * no errors;
  * no banned token in the candidate (`sorry`, `admit`, `native_decide`,
    `axiom`, `implemented_by`, `extern`, `unsafe`, `partial`, `opaque`,
    metaprogramming commands, `set_option debug...`): lexical, a cheap
    pre-check — the axiom report below is the authority;
  * the declaration's TYPE unchanged (pp.all, compared against the original
    file) — helpers inserted above it must not change what the spec means;
  * `#print axioms` of the declaration within propext / Classical.choice /
    Quot.sound, plus `sorryAx` only when the candidate opens new `vibe` holes
    (it is then "checked modulo those holes").
A spec defect is accepted only with a certificate theorem that compiles,
before the declaration, on the standard axioms.
"""
from __future__ import annotations

import argparse
import json
import os
import re
import shlex
import subprocess
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
PROMPT = HERE.parent / "prompts" / "vibe.md"
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
BANNED = [
    "sorry", "admit", "native_decide", "axiom", "implemented_by", "extern",
    "unsafe", "partial", "opaque", "run_cmd", "run_elab", "run_meta", "elab",
    "macro", "macro_rules", "syntax", "initialize", "builtin_initialize",
    "#eval", "#exit", "debug.skipKernelTC", "Lean.ofReduceBool", "Lean.trustCompiler",
]
DECL_START = re.compile(
    r"^(def |theorem |lemma |abbrev |instance|example|noncomputable |private |protected |"
    r"partial |opaque |structure |inductive |class |namespace |section|end\b|open |"
    r"@\[|/--|#|set_option |mutual|variable |attribute |universe )")
DEFAULT_LLM = "claude -p --dangerously-skip-permissions"


# --- text helpers -----------------------------------------------------------

def strip_comments(code: str) -> str:
    code = re.sub(r"/-.*?-/", " ", code, flags=re.S)
    code = re.sub(r"--[^\n]*", " ", code)
    return re.sub(r'"(\\.|[^"\\])*"', '""', code)


def banned_tokens(code: str) -> list[str]:
    text = strip_comments(code)
    found = []
    for tok in BANNED:
        pat = re.escape(tok)
        if tok[0].isalnum():
            pat = r"(?<![\w.'])" + pat
        if tok[-1].isalnum():
            pat = pat + r"(?![\w'])"
        if re.search(pat, text):
            found.append(tok)
    return found


def count_holes(code: str) -> int:
    return len(re.findall(r"(?<![\w.'])vibe(?![\w'])", strip_comments(code)))


def indent_after_first(text: str, col: int) -> str:
    lines = text.rstrip().split("\n")
    return "\n".join([lines[0]] + [(" " * col + l) if l.strip() else "" for l in lines[1:]])


def decl_end(lines: list[str], start: int) -> int:
    """Index of the first line after the declaration that contains line `start`."""
    for i in range(start + 1, len(lines)):
        if DECL_START.match(lines[i]):
            return i
    return len(lines)


# --- building the files to compile ------------------------------------------

def vibe_dir(req: dict) -> Path:
    return Path(req.get("vibe_dir") or Path(req["project_root"]) / ".vibe")


def load(req_path: str) -> dict:
    req = json.loads(Path(req_path).read_text())
    req["_lines"] = Path(req["source"]).read_text().split("\n")
    return req


def spliced(req: dict, cand: dict) -> tuple[str, int]:
    """The file cut after the target declaration, with the candidate in place
    of `vibe`; returns (text, line index where the declaration now starts)."""
    lines = req["_lines"]
    sl, sc, el, ec = req["start_line"] - 1, req["start_col"], req["end_line"] - 1, req["end_col"]
    end = decl_end(lines, sl)
    body = lines[: req["decl_start_line"]]
    helpers = (cand.get("helpers") or "").rstrip()
    if helpers:
        body += helpers.split("\n") + [""]
    decl_at = len(body)
    script = indent_after_first(cand["script"], sc)
    middle = lines[req["decl_start_line"]: sl] + [lines[sl][:sc] + script + lines[el][ec:]]
    body += middle + lines[el + 1: end]
    return "\n".join(body), decl_at


def original_cut(req: dict) -> str:
    lines = req["_lines"]
    return "\n".join(lines[: decl_end(lines, req["start_line"] - 1)])


def probes(decl: str) -> str:
    if decl == "_example" or not decl:
        return ""
    return (f"\nset_option pp.all true in\n#check @{decl}\n"
            f"#print axioms {decl}\n")


def compile_text(req: dict, text: str, name: str) -> tuple[int, str]:
    work = vibe_dir(req) / "work" / req["key"]
    work.mkdir(parents=True, exist_ok=True)
    path = work / f"{name}.lean"
    path.write_text(text)
    env = dict(os.environ, VIBE_MODE="offline")
    try:
        r = subprocess.run(["lake", "env", "lean", str(path)], cwd=req["project_root"],
                           capture_output=True, text=True, env=env,
                           timeout=int(os.environ.get("VIBE_CHECK_TIMEOUT", "600")))
    except subprocess.TimeoutExpired:
        return 124, "timeout"
    return r.returncode, (r.stdout + r.stderr).replace(str(path), name + ".lean")


def errors(out: str) -> list[str]:
    return [l for l in out.splitlines() if ": error:" in l or l.startswith("error:")]


def axioms_of(out: str, decl: str) -> set[str] | None:
    m = re.search(r"'" + re.escape(decl) + r"' depends on axioms: \[(.*?)\]", out, re.S)
    if m:
        return {a.strip() for a in m.group(1).split(",") if a.strip()}
    if f"'{decl}' does not depend on any axioms" in out:
        return set()
    return None


def signature(out: str, decl: str) -> str | None:
    # `#check @decl` under pp.all prints `decl : <type>` up to the axiom line.
    m = re.search(r"^@?" + re.escape(decl) + r" : (.*?)(?=\n'|\Z)", out, re.S | re.M)
    return re.sub(r"\s+", " ", m.group(1)).strip() if m else None


# --- the checker -------------------------------------------------------------

def check(req: dict, cand: dict) -> dict:
    kind = cand.get("kind", "solution")
    if kind == "spec_defect":
        return check_defect(req, cand)
    if not cand.get("script", "").strip():
        return {"ok": False, "reason": "candidate has no script"}
    code = (cand.get("helpers") or "") + "\n" + cand["script"]
    bad = banned_tokens(code)
    if bad:
        return {"ok": False, "reason": f"banned tokens: {bad}"}
    holes = count_holes(code)
    decl = req["decl_name"]
    text, _ = spliced(req, cand)
    rc, out = compile_text(req, text + probes(decl), "Check")
    errs = errors(out)
    if errs or rc not in (0,):
        return {"ok": False, "reason": "compile errors", "output": out[-6000:]}
    if decl == "_example":
        if holes == 0 and "declaration uses `sorry`" in out:
            return {"ok": False, "reason": "uses sorry", "output": out[-3000:]}
        return {"ok": True, "holes": holes, "axioms": None}
    axioms = axioms_of(out, decl)
    if axioms is None:
        return {"ok": False, "reason": "no axiom report", "output": out[-3000:]}
    allowed = STANDARD_AXIOMS | ({"sorryAx"} if holes else set())
    if not axioms <= allowed:
        return {"ok": False, "reason": f"axioms outside the whitelist: {sorted(axioms - allowed)}"}
    base = baseline_signature(req)
    new = signature(out, decl)
    if base is None or new is None or base != new:
        return {"ok": False, "reason": "the declaration's type changed (or could not be read)",
                "expected": base, "got": new}
    return {"ok": True, "holes": holes, "axioms": sorted(axioms)}


def baseline_signature(req: dict) -> str | None:
    cache = vibe_dir(req) / "work" / req["key"] / "baseline.sig"
    if cache.exists():
        return cache.read_text() or None
    _, out = compile_text(req, original_cut(req) + probes(req["decl_name"]), "Baseline")
    sig = signature(out, req["decl_name"]) or ""
    cache.write_text(sig)
    return sig or None


def check_defect(req: dict, cand: dict) -> dict:
    cert = cand.get("certificate", "")
    if cand.get("defect") not in ("unsat", "vacuous_pre", "vacuous_post"):
        return {"ok": False, "reason": "defect must be unsat | vacuous_pre | vacuous_post"}
    bad = banned_tokens(cert)
    if bad:
        return {"ok": False, "reason": f"banned tokens in certificate: {bad}"}
    m = re.search(r"^\s*theorem\s+(\S+)", cert, re.M)
    if not m:
        return {"ok": False, "reason": "certificate must be a `theorem`"}
    name = m.group(1)
    lines = req["_lines"][: req["decl_start_line"]]
    text = "\n".join(lines) + "\n\n" + cert + f"\n\n#print axioms {name}\n"
    rc, out = compile_text(req, text, "Defect")
    if errors(out) or rc != 0:
        return {"ok": False, "reason": "certificate does not compile", "output": out[-6000:]}
    axioms = axioms_of(out, name)
    if axioms is None or not axioms <= STANDARD_AXIOMS:
        return {"ok": False, "reason": f"certificate axioms: {axioms}"}
    return {"ok": True}


# --- the agent loop ------------------------------------------------------------

def render_prompt(req: dict, req_path: str, cand_path: Path, feedback: str) -> str:
    lines = req["_lines"]
    sl = req["start_line"] - 1
    numbered = "\n".join(f"{i + 1:5d}  {l}" for i, l in enumerate(lines))
    style = {
        "any": "Interleave code and proof, or write a plain function plus a theorem: whatever "
               "composes best here.",
        "coupled": "Keep code and proof together (e.g. build the subtype value with `⟨impl, proof⟩` "
                   "at every step, or recursive calls whose `.property` you use).",
        "split": "Write a plain function (as a helper) and a separate theorem about it, then build "
                 "the subtype from the two.",
    }.get(req.get("style", "any"), "")
    checker = f"python3 {shlex.quote(str(HERE / 'vibe_agent.py'))} check {shlex.quote(req_path)} {shlex.quote(str(cand_path))}"
    return (PROMPT.read_text()
            .replace("{file}", req["file"])
            .replace("{source}", req["source"])
            .replace("{numbered}", numbered)
            .replace("{line}", str(req["start_line"]))
            .replace("{col}", str(req["start_col"]))
            .replace("{vibe_line}", lines[sl])
            .replace("{decl_name}", req["decl_name"])
            .replace("{goal}", req["goal"])
            .replace("{hint}", req.get("hint") or "(none)")
            .replace("{style}", style)
            .replace("{candidate}", str(cand_path))
            .replace("{checker}", checker)
            .replace("{feedback}", feedback or "(first attempt)"))


def run(req_path: str, llm: str | None) -> int:
    req = load(req_path)
    root = Path(req["project_root"])
    key = req["key"]
    work = vibe_dir(req) / "work" / key
    cache = vibe_dir(req) / "cache"
    jobs = vibe_dir(req) / "jobs"
    for d in (work, cache, jobs):
        d.mkdir(parents=True, exist_ok=True)
    job = jobs / f"{key}.json"
    job.write_text(json.dumps({"pid": os.getpid(), "started": time.time()}))
    log = (work / "agent.log").open("a")
    llm = llm or os.environ.get("VIBE_LLM") or DEFAULT_LLM
    rounds = int(os.environ.get("VIBE_ROUNDS", "2"))
    timeout = int(os.environ.get("VIBE_TIMEOUT", "1800"))
    cand_path = work / "candidate.json"
    feedback = ""
    stale = cache / f"{key}.stale.json"
    if stale.exists():
        feedback = ("A previous result for this hole no longer checks in the current file "
                    "(the context changed). It was:\n" + stale.read_text())
    try:
        result = None
        for rnd in range(rounds):
            cand_path.unlink(missing_ok=True)
            prompt = render_prompt(req, req_path, cand_path, feedback)
            (work / f"prompt{rnd}.md").write_text(prompt)
            log.write(f"=== round {rnd}: {llm}\n"); log.flush()
            t0 = time.time()
            try:
                p = subprocess.run(shlex.split(llm), input=prompt, cwd=root, text=True,
                                   stdout=log, stderr=log, timeout=timeout)
                log.write(f"=== exit {p.returncode} after {time.time() - t0:.0f}s\n")
            except subprocess.TimeoutExpired:
                log.write("=== agent timed out\n")
            log.flush()
            if not cand_path.exists():
                feedback = "You did not write the candidate file."
                continue
            try:
                cand = json.loads(cand_path.read_text())
            except json.JSONDecodeError as e:
                feedback = f"The candidate file is not valid JSON: {e}"
                continue
            verdict = check(req, cand)
            log.write(f"=== check: {json.dumps(verdict)[:2000]}\n"); log.flush()
            if verdict["ok"]:
                result = entry(cand, verdict)
                break
            feedback = "The checker REJECTED your candidate:\n" + json.dumps(verdict, indent=2)
        if result is None:
            result = {"kind": "failure", "message": f"no candidate passed the checker in {rounds} "
                      f"round(s); see {work}/agent.log. Last: {feedback[:1500]}"}
        result["goal"] = req["goal"]
        result["decl_name"] = req["decl_name"]
        result["checked_at"] = time.strftime("%Y-%m-%dT%H:%M:%S")
        tmp = cache / f"{key}.json.tmp"
        tmp.write_text(json.dumps(result, indent=2, ensure_ascii=False))
        tmp.replace(cache / f"{key}.json")
        stale.unlink(missing_ok=True)
        return 0 if result["kind"] != "failure" else 1
    finally:
        job.unlink(missing_ok=True)
        log.close()


def entry(cand: dict, verdict: dict) -> dict:
    if cand.get("kind") == "spec_defect":
        return {"kind": "spec_defect", "defect": cand["defect"],
                "explanation": cand.get("explanation", ""), "certificate": cand["certificate"]}
    return {"kind": "solution", "script": cand["script"], "helpers": cand.get("helpers") or "",
            "notes": cand.get("notes", ""), "holes": verdict.get("holes", 0),
            "axioms": verdict.get("axioms"), "spec_check": cand.get("spec_check", "")}


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    sub = ap.add_subparsers(dest="cmd", required=True)
    r = sub.add_parser("run"); r.add_argument("request"); r.add_argument("--llm")
    c = sub.add_parser("check"); c.add_argument("request"); c.add_argument("candidate")
    a = ap.parse_args(argv)
    if a.cmd == "run":
        return run(a.request, a.llm)
    verdict = check(load(a.request), json.loads(Path(a.candidate).read_text()))
    print(json.dumps(verdict, indent=2))
    return 0 if verdict["ok"] else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
