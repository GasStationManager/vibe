import Vibe

/-! Remove duplicates, keeping exactly the same elements. -/

def dedup (xs : List Nat) : {ys : List Nat // ys.Nodup ∧ ∀ x, x ∈ ys ↔ x ∈ xs} := by
  vibe
