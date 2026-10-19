import Vibe

/-! Sorting: the output is ordered and a permutation of the input. -/

def sort (xs : List Int) : {ys : List Int // ys.Pairwise (· ≤ ·) ∧ ys.Perm xs} := by
  vibe
