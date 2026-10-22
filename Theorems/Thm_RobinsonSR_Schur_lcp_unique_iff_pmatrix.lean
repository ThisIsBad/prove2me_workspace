import Mathlib
import Definitions.Def_RobinsonSR_Schur_Setting

namespace RobinsonSR.Schur

/-- Robinson, p. 52, citing [6], for the LCP (3.8). -/
theorem lcp_unique_iff_pmatrix (s : ℕ) (M : Matrix (Fin s) (Fin s) ℝ) :
    (∀ z : Fin s → ℝ, ∃! w : Fin s → ℝ,
      (∀ j, 0 ≤ (M.mulVec w - z) j) ∧
      (∀ j, 0 ≤ w j) ∧
      w ⬝ᵥ (M.mulVec w - z) = 0) ↔ IsPMatrix M := by sorry

end RobinsonSR.Schur

