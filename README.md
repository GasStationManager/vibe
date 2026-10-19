# vibe: a Lean tactic for provably correct vibe coding

Write the specification as a Lean type, then write `by vibe`:

```lean
import Vibe

def listMax (xs : List Int) (h : xs ≠ []) : {m : Int // m ∈ xs ∧ ∀ x ∈ xs, x ≤ m} := by
  vibe
```

The parameters are the preconditions and the subtype is the postcondition.
`vibe` sends the goal, with the file it sits in, to an LLM agent. The agent
writes an implementation with its correctness proof. That result is checked
by Lean and then offered as a `Try this:` suggestion that replaces `vibe`:

```
vibe: checked. Try this:
  [apply] exact match xs, h with ...
```

The agent's own claims count for nothing: every result is compiled and checked
before it is cached, and re-run on the live goal before it is suggested. This
is a successor to [ProvablyCorrectVibeCoding](https://github.com/GasStationManager/ProvablyCorrectVibeCoding),
moved from a web app into the editor.

**Status: prototype.**

## How it works

```
 by vibe ──► goal + context + file ──► key ──► .vibe/cache/<key>.json ?
                                               │ hit: re-run the script on the live goal → Try this
                                               │ miss: scripts/vibe_agent.py run  (async by default)
                                               ▼
                         prompt (prompts/vibe.md) ──► LLM agent CLI (claude -p, codex, …)
                                               │ writes candidate.json, may call the checker itself
                                               ▼
                         checker: splice into a copy of the file, `lake env lean` it
                                               │ pass → cache entry; fail → feedback, next round
```

- **Code and proof together, or split; neither is required.** The result
  replaces the `vibe` token, so it is a tactic script. It can build the value
  and its proof together, e.g. `exact match xs with | … => ⟨…, by …⟩`, using
  recursive calls' `.property`. Or it can add helper declarations, such as a
  plain function and a theorem about it. `set_option vibe.style
  "any" | "coupled" | "split"` tells the agent which style to use (default `any`).
- **Helpers.** When the solution needs declarations above the current one,
  the suggestion's replacement span runs from the declaration's first line to
  the `vibe` token. The goal is closed with `sorry` until you accept it; at that
  point Lean re-checks everything.
- **Decomposition (plan mode).** For a large function the agent can return a
  plan instead of a finished proof. Each helper's body is another `by vibe`,
  with its own preconditions and a subtype postcondition, and the caller uses
  a helper only through `.val` and `.property`. The plan is checked now, modulo
  those holes. The suggestion says `checked modulo N new vibe hole(s)`, and
  each hole is filled later against its own spec.
- **The spec check.** The prompt asks the agent to examine the spec before
  writing any code, using the defect classes from SearchTool2's codeproof
  protocol:
  - **unsat**: no implementation meets the spec.
  - **vacuous_pre**: the preconditions never hold.
  - **vacuous_post**: every implementation meets the spec.

  A defect is reported only with a certificate: a `theorem` that compiles just
  above the declaration on the standard axioms. `vibe` then shows it as an
  error with the certificate. Testing, including property-based testing, is
  left to the agent.

## What the checker requires

`scripts/vibe_agent.py check REQUEST CANDIDATE`. The agent runs this itself
while it iterates, and the driver runs it again afterwards. It requires:

1. The file compiles with the candidate spliced in, cut after the target
   declaration. During the check, other `vibe` holes run with
   `VIBE_MODE=offline`, so they never start agents.
2. No banned token appears in the candidate: `sorry`, `admit`,
   `native_decide`, `axiom`, `partial`, `unsafe`, `opaque`, `implemented_by`,
   `extern`, the metaprogramming commands, or `debug.skipKernelTC`. This is a
   lexical pre-check.
3. The declaration's type, printed with `pp.all`, is identical to the type in
   the original file. This stops a helper, such as a `notation`, from changing
   what the spec means (there is a test for exactly that).
4. `#print axioms` of the declaration lists only `propext`,
   `Classical.choice` and `Quot.sound`, plus `sorryAx` only if the candidate
   opens new `vibe` holes.

On a cache hit for a solution without helpers, the tactic re-runs the script
on the live goal with error recovery off and refuses a `sorry` the script does
not account for. If the cached script no longer checks (the context changed),
the entry is moved to `<key>.stale.json` and the agent is asked again with the
old result as feedback.

## Install and use

Requires Lean `v4.35.0` (see `lean-toolchain`), Python 3, and an agent CLI that
reads a prompt on stdin and can run shell commands. The default is Claude Code
(`claude -p --dangerously-skip-permissions`).

```toml
# lakefile.toml of your project
[[require]]
name = "vibe"
git = "https://github.com/GasStationManager/vibe"
rev = "main"
```

Options:

| option | default | meaning |
|---|---|---|
| `vibe.mode` | `async` | `async`: start the agent in the background and close the goal with `sorry`; re-elaborate the file once the job finishes. `sync`: wait (use this for `lake build`). `offline`: cache only. The `VIBE_MODE` env var overrides it. |
| `vibe.llm` | `claude -p --dangerously-skip-permissions` | the agent CLI (or `VIBE_LLM`), e.g. `codex exec -` |
| `vibe.agent` | `python3 scripts/vibe_agent.py` (or the copy in `.lake/packages/vibe`) | the driver (or `VIBE_AGENT`) |
| `vibe.style` | `any` | `any` / `coupled` / `split` |

`vibe "use a two-pointer scan"` passes a hint, which is part of the cache key.
Environment variables: `VIBE_ROUNDS` (agent rounds, default 2), `VIBE_TIMEOUT`
(seconds per round, default 1800), `VIBE_CHECK_TIMEOUT` (default 600).

Files: `.vibe/cache/` holds results; commit it if you want others to get cache
hits. `.vibe/work/<key>/` holds the request, prompts, `agent.log` and the
check files. `.vibe/jobs/` lists running jobs. If a job dies, delete its file
there. To retry a failure, delete its cache entry or change the hint.

Only `lake build` the `Vibe` library; it is the default target. The
`Examples` library (`ListMax`, `Dedup`, `Sort`) contains `vibe` holes. Its
results are committed in `.vibe/cache`, so `VIBE_MODE=offline lake build
Examples` replays them without a model. `ExamplesDefect/BadSpec.lean` has an
unsatisfiable spec on purpose; `lake env lean ExamplesDefect/BadSpec.lean`
shows the certified defect.

The example runs, on Claude Code as the agent: each solution passed the checker
on the first round, in 17–24 s per hole. Sort used the library's `mergeSort`
and its lemmas; Dedup and ListMax are recursive with code and proof
interleaved.

## Tests

```
lake build
python3 -m unittest discover -s tests -v
```

The tests use `tests/fake_llm.py` instead of a model. They cover: a solution
checked and suggested, then served from the cache; a wrong first round
followed by a correct one; refusing `sorry` and `native_decide`; a helper
suggestion spanning the whole declaration; a helper that changes the spec
being refused; a certified spec defect; a bogus certificate being refused;
plan mode with a nested `vibe` hole; a stale cache entry triggering a re-ask;
async mode; offline mode.

## Known limits

- Finding the declaration's start (where helpers go) and its end (where the
  check cuts the file) is a heuristic over column-0 keywords.
- The cache key is the pretty-printed goal plus the declaration name, hint and
  style. A changed definition that the goal only mentions does not change the
  key; the re-run on a cache hit catches that.
- A spec-defect certificate is checked to compile, not to be about *this*
  spec. The certificate is shown in full so you can judge it. (SearchTool2's
  codeproof does the stronger check.)
- The cache is trusted for helper suggestions until you accept them, and once
  accepted it is ordinary Lean. Do not use a `.vibe/cache` from a source you
  do not trust.
- In async mode the editor does not refresh itself when a job finishes; edit
  the file or restart it.
- Backends 2 and 3 from the design (an agent with tools in a scratch copy is
  what runs now; a SearchTool2 tree for large tasks) are not separate yet:
  any CLI agent can be plugged in through `vibe.llm`.
