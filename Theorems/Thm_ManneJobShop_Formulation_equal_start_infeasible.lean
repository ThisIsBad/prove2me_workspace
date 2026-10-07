import Mathlib

namespace ManneJobShop.Formulation

/-- Manne (1960), p. 220: if `x_j = x_k` (both equal to `x`) and the durations are positive, no
integer `y_jk` with `0 ≤ y_jk ≤ 1` satisfies both (3) and (4). -/
theorem equal_start_infeasible (T aj ak x : ℤ) (haj : 0 < aj) (hak : 0 < ak) :
    ¬ ∃ y : ℤ, (0 ≤ y ∧ y ≤ 1) ∧
        (T + ak) * y + (x - x) ≥ ak ∧ (T + aj) * (1 - y) + (x - x) ≥ aj := by sorry

end ManneJobShop.Formulation

