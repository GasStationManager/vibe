# vibe: implement a specified function, with its proof

You are filling ONE `vibe` hole in a Lean 4 file. The hole's goal type IS the
specification: read the declaration's parameters as the PRECONDITIONS and its
return type — usually a subtype `{y : T // P x y}` — as the POSTCONDITION. Your
job is an implementation that meets it, with the proof, as Lean that checks.

## Where

- File: `{file}` (a snapshot of the editor buffer is at `{source}`; the
  project root is your working directory, and `lake env lean <file>` compiles)
- Declaration: `{decl_name}`
- The hole: line {line}, column {col}:

```
{vibe_line}
```

- Its goal, with local context:

```
{goal}
```

- User hint: {hint}

The whole file, numbered:

```lean
{numbered}
```

## First: the spec check

The specification can itself be wrong, and no implementation fixes that. Read
it as `pre x → post x (impl x)`. Exactly these defects count:

- **unsat** — `¬ ∃ impl, ∀ x, pre x → post x (impl x)`: no implementation
  meets it (often: one input on which every output fails the postcondition).
- **vacuous_pre** — `¬ ∃ x, pre x`: the preconditions never hold.
- **vacuous_post** — `∀ impl, ∀ x, pre x → post x (impl x)`: the
  postcondition constrains nothing; every implementation meets it.

A trivial implementation (a constant, `default`) that happens to meet the spec
is NOT by itself a defect — it may be exactly what is asked; it is how you look
for `vacuous_post`. Only report a defect you can PROVE: the certificate is a
Lean `theorem` stating the defect for this spec, compiled just above the
declaration (so it may use everything defined before it, never the
declaration itself), on the standard axioms. If you only suspect a defect,
implement the spec as written and say so in `notes`.

Think about the spec before you start coding. Testing (`#eval`, `#guard`,
property-based testing if the project has Plausible) is your call — do it in
scratch files, never in the user's file.

## Then: the implementation and proof

- {style}
- The result replaces the single token `vibe` (so it is a TACTIC SCRIPT, e.g.
  `exact ⟨impl, proof⟩`, `refine ⟨fun .. => .., ?_⟩ ...`, or
  `exact match n with | ...`). Recursion on `{decl_name}` itself works from a
  tactic script (`exact match xs with | [] => .. | x :: t => .. ({decl_name} t).property ..`),
  with `termination_by`/`decreasing_by` if needed.
- Helper declarations, if you need them, go in `helpers`: they are inserted
  above the declaration (and its doc comment/attributes). Name them so they
  cannot clash (e.g. prefix `{decl_name}_`).
- It must be computable code (no `noncomputable`, no `Classical.choice` in the
  data), and must NOT use: `sorry`, `admit`, `native_decide`, `axiom`,
  `partial`, `unsafe`, `opaque`, `implemented_by`, `extern`, metaprogramming
  commands, or `set_option debug.*`. Do not change the declaration's
  signature: the checker compares its type before and after.
- Do not edit the user's file. Work in scratch files under `.vibe/work/`.

### Large tasks: decompose with more `vibe` holes

If the function is large, you may return a PLAN instead of a finished proof:
helpers whose bodies are themselves `by vibe`, each with its own spec as
preconditions (parameters) and a subtype postcondition, e.g.

```lean
def {decl_name}_merge (a b : List Nat) (ha : ...) (hb : ...) : {ys : List Nat // ...} := by
  vibe
```

and a script that uses each helper ONLY through its spec (`.val`, `.property`).
Your script must check now, modulo those holes; each hole is then filled by a
later `vibe` call against its own spec, so a helper spec must be TRUE and
STRONG ENOUGH for the caller. Prefer a finished solution when you can get one.

## Output

Write a JSON file to `{candidate}`, one of:

```json
{"kind": "solution",
 "spec_check": "one sentence: what you checked about the spec",
 "helpers": "Lean declarations to insert above the declaration, or empty",
 "script": "the tactic script that replaces `vibe`",
 "notes": "anything the user should know (assumptions, suspected spec weakness)"}
```

```json
{"kind": "spec_defect",
 "defect": "unsat | vacuous_pre | vacuous_post",
 "explanation": "the defect in one or two sentences, with the witness input",
 "certificate": "theorem ... : ... := ..."}
```

Write `script` with its own relative indentation, first line unindented; it is
indented to the hole's column when spliced.

Before you finish, run the checker, which is exactly what will judge you:

```
{checker}
```

It prints `"ok": true` or the reason it refused. Iterate until it passes.

## Feedback from earlier attempts

{feedback}
