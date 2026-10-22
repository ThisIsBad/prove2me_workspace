import Mathlib
import Definitions.Def_RobinsonSR_Schur_Setting

namespace RobinsonSR.Schur

/-- Robinson, Theorem 3.1, p. 51. -/
theorem theorem_3_1 (r s : ℕ) (hr : 0 < r) (hs : 0 < s)
    (A₁₁ : Matrix (Fin r) (Fin r) ℝ)
    (A₁₂ : Matrix (Fin r) (Fin s) ℝ)
    (A₂₁ : Matrix (Fin s) (Fin r) ℝ)
    (A₂₂ : Matrix (Fin s) (Fin s) ℝ) :
    (∀ K : Set (EuclideanSpace ℝ (Fin s)), K.Nonempty → IsClosed K → Convex ℝ K →
      A₁₁.det ≠ 0 → PosDefNS (schur A₁₁ A₁₂ A₂₁ A₂₂) →
      InvIsLipschitzFunction (Matrix.fromBlocks A₁₁ A₁₂ A₂₁ A₂₂) (prodSet K)) ∧
    (InvIsLipschitzFunction (Matrix.fromBlocks A₁₁ A₁₂ A₂₁ A₂₂)
        (prodSet (nonnegOrthant s)) ↔
      A₁₁.det ≠ 0 ∧ IsPMatrix (schur A₁₁ A₁₂ A₂₁ A₂₂)) := by sorry

end RobinsonSR.Schur

