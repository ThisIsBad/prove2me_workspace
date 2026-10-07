import Mathlib

namespace ManneJobShop.Formulation

/-- Manne (1960), p. 220, conditions (1)–(4): when `|x_j - x_k| ≤ T`, some integer `y_jk` with
`0 ≤ y_jk ≤ 1` satisfies (3) and (4) iff the either-or condition (1) holds. -/
theorem pair_either_or_iff (T aj ak xj xk : ℤ) (hT : |xj - xk| ≤ T) :
    (∃ y : ℤ, (0 ≤ y ∧ y ≤ 1) ∧
        (T + ak) * y + (xj - xk) ≥ ak ∧ (T + aj) * (1 - y) + (xk - xj) ≥ aj) ↔
      (xj - xk ≥ ak ∨ xk - xj ≥ aj) := by sorry

end ManneJobShop.Formulation

