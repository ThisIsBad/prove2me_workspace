import Mathlib

namespace ManneJobShop.Formulation

/-- Manne (1960), p. 222: the `y_jk` must be discrete. With `y_jk` relaxed to a real number in
`[0, 1]`, and positive durations not exceeding `T`, conditions (3) and (4) can be met with
`x_j = x_k = x`, although the either-or condition (1) fails there. -/
theorem relaxation_admits_overlap (T aj ak x : ℝ) (haj : 0 < aj) (hak : 0 < ak)
    (hajT : aj ≤ T) (hakT : ak ≤ T) :
    (∃ y : ℝ, (0 ≤ y ∧ y ≤ 1) ∧
        (T + ak) * y + (x - x) ≥ ak ∧ (T + aj) * (1 - y) + (x - x) ≥ aj) ∧
      ¬ (x - x ≥ ak ∨ x - x ≥ aj) := by sorry

end ManneJobShop.Formulation

