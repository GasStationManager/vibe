import Lean

/-!
# The `vibe` tactic

`vibe` fills a goal whose TYPE is the specification — typically the body of
a definition whose return type is a subtype (the postcondition) and whose
parameters carry the preconditions:

```lean
def dedup (xs : List Nat) : {ys : List Nat // ys.Nodup ∧ ∀ x, x ∈ ys ↔ x ∈ xs} := by
  vibe
```

The implementation and its proof come from an external LLM agent
(`scripts/vibe_agent.py`). Nothing the agent says is trusted: every result is
checked by Lean, and what reaches the user is a `Try this:` suggestion that
replaces `vibe` with checked code.

Results are cached under `.vibe/cache/<key>.json`, keyed on the goal (with its
local context), the declaration name, the hint and the style, so re-elaboration
does not call the agent again. On a cache hit the cached script is re-run here,
against the live goal; a cached script that no longer checks is treated as a
miss and handed back to the agent with the errors.

Modes (`set_option vibe.mode`, or the `VIBE_MODE` environment variable, which
wins):
* `async` (default) — on a miss, start the agent in the background and close
  the goal with `sorry`; the result appears on the next elaboration.
* `sync` — on a miss, run the agent and wait (for `lake build`).
* `offline` — never start the agent; use the cache or leave a `sorry`.
-/

open Lean Elab Tactic Meta

namespace Vibe

register_option vibe.mode : String := {
  defValue := "async"
  descr := "vibe: what to do on a cache miss: async | sync | offline" }

register_option vibe.agent : String := {
  defValue := ""
  descr := "vibe: command that runs the vibe agent (default: python3 scripts/vibe_agent.py, \
    or the copy under .lake/packages/vibe)" }

register_option vibe.llm : String := {
  defValue := ""
  descr := "vibe: the LLM agent CLI the vibe agent drives, reading its prompt on stdin \
    (default: claude -p)" }

register_option vibe.style : String := {
  defValue := "any"
  descr := "vibe: any | coupled | split — whether code and proof may be interleaved \
    (coupled), must be a plain function plus a theorem (split), or either (any)" }

/-- `vibe` asks an LLM agent for an implementation with its correctness proof.
`vibe "hint"` passes a hint to the agent. -/
syntax (name := vibeTac) "vibe" (ppSpace str)? : tactic

/-! ## Configuration -/

/-- The state directory: `.vibe` under the working directory, or `VIBE_DIR`. -/
def vibeDir : IO System.FilePath := do
  match ← IO.getEnv "VIBE_DIR" with
  | some d => if d != "" then return d else return ".vibe"
  | none => return ".vibe"
def cacheDir : IO System.FilePath := return (← vibeDir) / "cache"
def workDir : IO System.FilePath := return (← vibeDir) / "work"
def jobsDir : IO System.FilePath := return (← vibeDir) / "jobs"

def mode : CoreM String := do
  if let some m ← IO.getEnv "VIBE_MODE" then
    if m != "" then return m
  return vibe.mode.get (← getOptions)

def agentCommand : CoreM (String × Array String) := do
  let opt := vibe.agent.get (← getOptions)
  let cmd ← if opt != "" then pure opt else
    match ← IO.getEnv "VIBE_AGENT" with
    | some c => if c != "" then pure c else defaultCmd
    | none => defaultCmd
  let parts := (cmd.splitOn " ").filter (· != "") |>.toArray
  return (parts[0]!, parts.extract 1 parts.size)
where
  defaultCmd : CoreM String := do
    let local_ : System.FilePath := "scripts" / "vibe_agent.py"
    if ← local_.pathExists then return s!"python3 {local_}"
    return s!"python3 {System.FilePath.mk ".lake" / "packages" / "vibe" / "scripts" / "vibe_agent.py"}"

/-! ## Source positions -/

def declPrefixes : List String :=
  ["def ", "theorem ", "lemma ", "abbrev ", "instance", "example", "noncomputable ",
   "private ", "protected ", "partial ", "opaque ", "@["]

def startsDecl (l : String) : Bool := declPrefixes.any (l.startsWith ·)

/-- The first line (0-based) of the declaration containing line `line`:
the nearest line above it that opens a declaration at column 0, extended
upwards over attribute lines and a doc comment. Helpers are inserted here.
A heuristic over text, like the agent's truncation; both read only lines. -/
def declStartLine (lines : Array String) (line : Nat) : Nat := Id.run do
  let mut i := line
  while i > 0 && !startsDecl lines[i]! do
    i := i - 1
  while i > 0 && lines[i-1]!.startsWith "@[" do
    i := i - 1
  if i > 0 && lines[i-1]!.trimAsciiEnd.toString.endsWith "-/" then
    let mut j := i - 1
    while j > 0 && !lines[j]!.startsWith "/-" do
      j := j - 1
    if lines[j]!.startsWith "/--" then i := j
  return i

/-- Indent every line after the first by `col` spaces. -/
def indentAfterFirst (text : String) (col : Nat) : String :=
  let pad := "".pushn ' ' col
  match text.trimAsciiEnd.toString.splitOn "\n" with
  | [] => ""
  | l :: ls => String.intercalate "\n" (l :: ls.map fun (s : String) => if s.trimAscii.isEmpty then "" else pad ++ s)

/-- Erase source positions, so a parsed script's errors point at `vibe`. -/
partial def eraseInfo (info : SourceInfo) : Syntax → Syntax
  | .node _ k args => .node info k (args.map (eraseInfo info))
  | .atom _ v => .atom info v
  | .ident _ raw v pre => .ident info raw v pre
  | .missing => .missing

/-! ## Cache entries -/

inductive Entry where
  | solution (script helpers notes : String) (holes : Nat)
  | specDefect (defect explanation certificate : String)
  | failure (message : String)

def readEntry (key : String) : IO (Option Entry) := do
  let path := (← cacheDir) / s!"{key}.json"
  unless ← path.pathExists do return none
  let some j := (Json.parse (← IO.FS.readFile path)).toOption | return none
  let str (f : String) : String := (j.getObjValAs? String f).toOption.getD ""
  match str "kind" with
  | "solution" =>
    let holes := (j.getObjValAs? Nat "holes").toOption.getD 0
    return some (.solution (str "script") (str "helpers") (str "notes") holes)
  | "spec_defect" => return some (.specDefect (str "defect") (str "explanation") (str "certificate"))
  | "failure" => return some (.failure (str "message"))
  | _ => return none

/-- Move a cache entry aside (it no longer checks); the agent gets it as feedback. -/
def retire (key : String) : IO Unit := do
  let path := (← cacheDir) / s!"{key}.json"
  if ← path.pathExists then
    IO.FS.rename path ((← cacheDir) / s!"{key}.stale.json")

/-! ## Running a script on the live goal -/

/-- Run `script` on `g`. `none` = closed it (no `sorry` unless the script
itself contains `vibe` holes); `some err` = it did not, state restored. -/
def tryScript (g : MVarId) (script : String) (ref : Syntax) : TacticM (Option String) := do
  -- `tacticSeq` is not a parser category: parse `by <script>` as a term.
  let stx ← match Parser.runParserCategory (← getEnv) `term ("by\n  " ++ indentAfterFirst script 2) "<vibe>" with
    | .ok stx => pure stx[1]
    | .error e => return some s!"parse error: {e}"
  let s ← saveState
  try
    setGoals [g]
    Term.withoutErrToSorry <| withoutRecover <| withRef ref <|
      evalTactic (eraseInfo (SourceInfo.fromRef ref) stx)
    let rest ← getUnsolvedGoals
    unless rest.isEmpty do
      let goals ← rest.mapM fun m => return toString (← ppGoal m)
      s.restore (restoreInfo := true)
      return some s!"unsolved goals:\n{String.intercalate "\n\n" goals}"
    let pf ← instantiateMVars (mkMVar g)
    let nested := (script.splitOn "vibe").length > 1
    if pf.hasSorry && !nested then
      s.restore (restoreInfo := true)
      return some "the script closes the goal with `sorry`"
    return none
  catch e =>
    let msg ← e.toMessageData.toString
    s.restore (restoreInfo := true)
    return some msg

/-! ## The tactic -/

structure Site where
  key : String
  goal : String
  declName : String
  hint : String
  style : String
  fileName : String
  source : String
  lines : Array String
  startLine : Nat   -- 1-based
  startCol : Nat    -- codepoints, 0-based
  endLine : Nat
  endCol : Nat
  declStart : Nat   -- 0-based line

def hexKey (s : String) : String :=
  let h1 := hash s
  let h2 := mixHash h1 (hash (s ++ "#vibe"))
  let hex (n : UInt64) := String.ofList (Nat.toDigits 16 n.toNat)
  hex h1 ++ hex h2

def mkSite (stx : Syntax) (g : MVarId) (hint : String) : TacticM Site := do
  let goal := toString (← ppGoal g)
  let declName := (← Term.getDeclName?).map toString |>.getD "_example"
  let style := vibe.style.get (← getOptions)
  let fm ← getFileMap
  let src := fm.source
  let lines := (src.splitOn "\n").toArray
  let p := fm.toPosition (stx.getPos?.getD 0)
  let q := fm.toPosition (stx.getTailPos?.getD 0)
  return {
    key := hexKey s!"{goal}\x00{declName}\x00{hint}\x00{style}"
    goal, declName, hint, style, fileName := ← getFileName, source := src, lines
    startLine := p.line, startCol := p.column, endLine := q.line, endCol := q.column
    declStart := declStartLine lines (p.line - 1) }

def writeRequest (site : Site) : IO System.FilePath := do
  let dir := (← workDir) / site.key
  IO.FS.createDirAll dir
  IO.FS.createDirAll (← cacheDir)
  IO.FS.createDirAll (← jobsDir)
  IO.FS.writeFile (dir / "source.lean") site.source
  let req := Json.mkObj [
    ("key", site.key), ("goal", site.goal), ("decl_name", site.declName),
    ("hint", site.hint), ("style", site.style), ("file", site.fileName),
    ("source", toString (dir / "source.lean")),
    ("start_line", site.startLine), ("start_col", site.startCol),
    ("end_line", site.endLine), ("end_col", site.endCol),
    ("decl_start_line", site.declStart),
    ("project_root", toString (← IO.currentDir)),
    ("vibe_dir", toString (← IO.FS.realPath (← vibeDir)))]
  let path := dir / "request.json"
  IO.FS.writeFile path req.pretty
  return path

def withLlm (args : Array String) : CoreM (Array String) := do
  let llm := vibe.llm.get (← getOptions)
  return if llm == "" then args else args ++ #["--llm", llm]

/-- The `Try this:` for a solution that needs declarations above this one:
the replaced span runs from the declaration's first line to the end of `vibe`. -/
def suggestWithHelpers (stx : Syntax) (site : Site) (script helpers : String) : TacticM Unit := do
  let fm ← getFileMap
  let startPos := fm.ofPosition ⟨site.declStart + 1, 0⟩
  let endPos := stx.getTailPos?.getD 0
  let span := Syntax.atom (.synthetic startPos endPos) ""
  let before := site.lines.extract site.declStart (site.startLine - 1) |>.toList
  let vibeLine := (site.lines[site.startLine - 1]!).take site.startCol
  let text := helpers.trimAsciiEnd.toString ++ "\n\n" ++
    String.intercalate "\n" (before ++ [vibeLine.toString ++ indentAfterFirst script site.startCol])
  Lean.Meta.Tactic.TryThis.addSuggestion stx { suggestion := .string text } (origSpan? := some span)
    (header := "vibe: Try this (adds helper declarations above):")

partial def evalVibeCore (stx : Syntax) (hint : String) (attempt : Nat) : TacticM Unit := do
  let g ← getMainGoal
  let site ← mkSite stx g hint
  match ← readEntry site.key with
  | some (.solution script helpers notes holes) =>
    let notes := if notes.isEmpty then "" else s!"\nAgent notes: {notes}"
    if helpers.trimAscii.isEmpty then
      match ← tryScript g script stx with
      | none =>
        let modulo := if holes > 0 then s!" modulo {holes} new `vibe` hole(s)" else ""
        Lean.Meta.Tactic.TryThis.addSuggestion stx { suggestion := .string (indentAfterFirst script site.startCol) }
          (header := s!"vibe: checked{modulo}. Try this:")
        unless notes.isEmpty do logInfoAt stx notes
      | some err =>
        retire site.key
        if attempt == 0 then
          logInfoAt stx m!"vibe: cached result no longer checks, asking again:\n{err}"
          evalVibeCore stx hint 1
        else
          throwError "vibe: result does not check here:\n{err}"
    else
      g.admit
      suggestWithHelpers stx site script helpers
      logWarningAt stx m!"vibe: the solution adds helper declarations, so it cannot be \
        run here; it was checked by the agent's checker. Accept the suggestion and Lean \
        re-checks it.{notes}"
  | some (.specDefect defect explanation certificate) =>
    g.admit
    logErrorAt stx m!"vibe: SPEC DEFECT ({defect}): {explanation}\n\
      Lean-checked certificate (check that it states the defect of THIS spec):\n{certificate}\n\
      Fix the specification, or delete .vibe/cache/{site.key}.json and pass a hint."
  | some (.failure message) =>
    g.admit
    logErrorAt stx m!"vibe: the agent gave up: {message}\n\
      Retry by deleting .vibe/cache/{site.key}.json, or pass a hint: vibe \"...\""
  | none =>
    let jobFile := (← jobsDir) / s!"{site.key}.json"
    if ← jobFile.pathExists then
      g.admit
      logWarningAt stx m!"vibe: job {site.key} is running; re-elaborate when it finishes \
        (or delete {jobFile} if it died)"
      return
    match ← mode with
    | "offline" =>
      g.admit
      logWarningAt stx m!"vibe: no cached result for {site.key} (offline)"
    | "sync" =>
      let req ← writeRequest site
      let (cmd, args) ← agentCommand
      let args ← withLlm (args ++ #["run", toString req])
      let out ← IO.Process.output { cmd, args }
      if (← readEntry site.key).isNone then
        throwError "vibe: agent produced no result (exit {out.exitCode}):\n{out.stderr}\n{out.stdout}"
      if attempt > 1 then throwError "vibe: no checked result"
      evalVibeCore stx hint (attempt + 1)
    | _ =>
      let req ← writeRequest site
      let (cmd, args) ← agentCommand
      let args ← withLlm (args ++ #["run", toString req])
      let _ ← IO.Process.spawn { cmd, args, stdin := .null, stdout := .null, stderr := .null }
      g.admit
      logWarningAt stx m!"vibe: started job {site.key}; the result appears on the next \
        elaboration of this file"

@[tactic vibeTac] def evalVibe : Tactic := fun stx => do
  let hint := match stx[1].getOptional? with
    | some s => s.isStrLit?.getD ""
    | none => ""
  evalVibeCore stx hint 0

end Vibe
