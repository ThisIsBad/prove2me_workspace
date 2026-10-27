import Mathlib
import Definitions.Def_AlmostSSDPortfolio_AASSD_Model
open MeasureTheory Set

namespace AlmostSSDPortfolio.AASSD

theorem proposition_1 {n T Tb : ℕ} (S : Setting n T Tb) (hS : S.Standing)
    (D : Discretization S) (lam : Fin n → ℝ) (hlam : lam ∈ simplex n) :
    ∀ x : ℝ, S.F2 lam x ≤ D.hatF2 lam x := by sorry

end AlmostSSDPortfolio.AASSD

