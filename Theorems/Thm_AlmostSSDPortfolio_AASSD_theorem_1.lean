import Mathlib
import Definitions.Def_AlmostSSDPortfolio_AASSD_Model
open MeasureTheory Set

namespace AlmostSSDPortfolio.AASSD

theorem theorem_1 {n T Tb : ℕ} (S : Setting n T Tb) (hS : S.Standing)
    (lam : Fin n → ℝ) (hlam : lam ∈ simplex n) (τ : ℝ) (hτ : 1 < τ)
    (h : ∃ D : Discretization S, D.IsAASSD lam τ) : S.IsASSD lam τ := by sorry

end AlmostSSDPortfolio.AASSD

