import Lean
import Vibe.Tactic

/-!
# The lightbulb for a finished job

A job's result is reported by a snapshot task (`Vibe.watchJob`), and a task
cannot add info-tree nodes, so the `Try this` it posts has no code action
behind it until the file is elaborated again. This provider closes that gap:
at a `vibe` the tactic left a `PendingInfo` on, it reads the job's cache entry
and offers the edit. It offers nothing for a job still running, a spec defect
or a failure.
-/

open Lean Elab Server Lsp RequestM

namespace Vibe

@[code_action_provider] def pendingProvider : CodeActionProvider := fun params snap => do
  let doc ← readDoc
  let text := doc.meta.text
  let pending := snap.infoTree.foldInfo (init := #[]) fun _ info acc =>
    match info with
    | .ofCustomInfo { stx, value } =>
      match value.get? PendingInfo with
      | some p => acc.push (stx, p)
      | none => acc
    | _ => acc
  let mut out := #[]
  for (stx, p) in pending do
    let some r := stx.getRange? | continue
    let range := text.utf8RangeToLspRange r
    unless range.start.line ≤ params.range.end.line && params.range.start.line ≤ range.end.line do
      continue
    let some (.solution script helpers _ _) ← (readEntry p.key : IO _) | continue
    let (range, newText) :=
      if helpers.trimAscii.isEmpty then (range, indentAfterFirst script p.col)
      else ({ range with start := text.utf8PosToLspPos p.declStart },
            helperText p.declPrefix p.col script helpers)
    out := out.push {
      eager := {
        title := if helpers.trimAscii.isEmpty then "vibe: apply the checked result"
          else "vibe: apply the checked result (adds helper declarations above)"
        kind? := "quickfix"
        edit? := some <| .ofTextEdit doc.versionedIdentifier { range, newText } } }
  return out

end Vibe
