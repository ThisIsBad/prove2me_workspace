import Mathlib
import Definitions.Def_AlmostSSDPortfolio_AASSD_Model
open MeasureTheory Set

namespace AlmostSSDPortfolio.AASSD

theorem step_12b {n T Tb : ℕ} (S : Setting n T Tb) (hS : S.Standing)
    (D : Discretization S) (lam : Fin n → ℝ) (hlam : lam ∈ simplex n) :
    ∫ t in S.S2 lam, (S.F2 lam t - S.G2 t) ≤ ∫ t in D.hatS2 lam, (D.hatF2 lam t - S.G2 t) := by sorry

end AlmostSSDPortfolio.AASSD

