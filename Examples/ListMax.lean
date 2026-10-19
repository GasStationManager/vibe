import Vibe

/-! A list's maximum: the precondition is a parameter, the postcondition a subtype. -/

def listMax (xs : List Int) (h : xs ≠ []) : {m : Int // m ∈ xs ∧ ∀ x ∈ xs, x ≤ m} := by
  vibe
