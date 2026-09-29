import Mathlib
import Definitions.Def_LassoDantzig_Equivalence_Model

namespace LassoDantzig.Equivalence

/-- (2.3): every Lasso solution satisfies the Dantzig constraint. -/
theorem eq_2_3_lasso_dantzig_feasible {n M : ℕ} (hn : 1 ≤ n)
    (X : Matrix (Fin n) (Fin M) ℝ) (y : Fin n → ℝ) (r : ℝ) (hr : 0 < r)
    (βL : Fin M → ℝ) (hL : IsLasso X y r βL) :
    DantzigFeasible X y r βL := by sorry

end LassoDantzig.Equivalence
