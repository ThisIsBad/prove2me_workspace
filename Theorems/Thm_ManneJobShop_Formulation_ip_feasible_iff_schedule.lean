import Mathlib
import Definitions.Def_ManneJobShop_Formulation_Model

namespace ManneJobShop.Formulation

/-- Manne (1960), pp. 220–221: for fixed start days `x` and bound `t`, the integer program
(2)–(7) has a solution `y` iff `x` is a schedule (horizon, (1), (5a), (5c), (6)) satisfying (7). -/
theorem ip_feasible_iff_schedule {n : ℕ} (I : Instance n) (x : Fin n → ℤ) (t : ℤ) :
    (∃ y : Fin n → Fin n → ℤ, IsIPFeasible I x y t) ↔
      (IsSchedule I x ∧ ∀ j, x j + I.a j ≤ t) := by sorry

end ManneJobShop.Formulation

