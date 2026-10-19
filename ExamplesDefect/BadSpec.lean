import Vibe

/-! A specification no implementation can meet: `vibe` should certify the defect. -/

def between (lo hi : Nat) : {m : Nat // lo ≤ m ∧ m < hi ∧ hi ≤ lo + 0} := by
  vibe
