import Mathlib

namespace TalagrandConc.QPoints

/-- Talagrand's `a(q, α)` of (3.2.2): the largest `x > 1` with
`x + q α x^{-1/α} ≤ 1 + q α`. For `q ≥ 2` and `α ≥ 1` this set is `(1, a]`, so `a(q, α)`
is the unique `x > 1` solving `x + q α x^{-1/α} = 1 + q α`. -/
noncomputable def aConst (q : ℕ) (α : ℝ) : ℝ :=
  sSup {x : ℝ | 1 < x ∧ x + (q : ℝ) * α * x ^ (-(1 / α)) ≤ 1 + (q : ℝ) * α}

end TalagrandConc.QPoints
