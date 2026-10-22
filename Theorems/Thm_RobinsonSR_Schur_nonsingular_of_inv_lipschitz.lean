import Mathlib
import Definitions.Def_RobinsonSR_Schur_Setting

namespace RobinsonSR.Schur

/-- Robinson, p. 52, necessity of condition (1). -/
theorem nonsingular_of_inv_lipschitz (r s : ℕ) (hr : 0 < r) (hs : 0 < s)
    (A₁₁ : Matrix (Fin r) (Fin r) ℝ)
    (A₁₂ : Matrix (Fin r) (Fin s) ℝ)
    (A₂₁ : Matrix (Fin s) (Fin r) ℝ)
    (A₂₂ : Matrix (Fin s) (Fin s) ℝ)
    (h : InvIsLipschitzFunction (Matrix.fromBlocks A₁₁ A₁₂ A₂₁ A₂₂)
      (prodSet (nonnegOrthant s))) :
    A₁₁.det ≠ 0 := by sorry

end RobinsonSR.Schur

