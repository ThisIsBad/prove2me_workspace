import Mathlib
import Definitions.Def_RobinsonSR_Schur_Setting

namespace RobinsonSR.Schur

/-- Robinson, p. 51, equations (3.5)-(3.7). -/
theorem inclusion_iff_schur (r s : ℕ) (hr : 0 < r) (hs : 0 < s)
    (A₁₁ : Matrix (Fin r) (Fin r) ℝ)
    (A₁₂ : Matrix (Fin r) (Fin s) ℝ)
    (A₂₁ : Matrix (Fin s) (Fin r) ℝ)
    (A₂₂ : Matrix (Fin s) (Fin s) ℝ)
    (hA₁₁ : A₁₁.det ≠ 0) (K : Set (EuclideanSpace ℝ (Fin s)))
    (y w : EuclideanSpace ℝ (Fin r ⊕ Fin s)) :
    (y - (Matrix.fromBlocks A₁₁ A₁₂ A₂₁ A₂₂).toEuclideanLin w ∈
      normalCone (prodSet K) w) ↔
    (upperBlock w = (A₁₁⁻¹).toEuclideanLin (upperBlock y) -
      (A₁₁⁻¹).toEuclideanLin (A₁₂.toEuclideanLin (lowerBlock w))) ∧
    (lowerBlock y - A₂₁.toEuclideanLin ((A₁₁⁻¹).toEuclideanLin (upperBlock y)) -
      (schur A₁₁ A₁₂ A₂₁ A₂₂).toEuclideanLin (lowerBlock w) ∈
      normalCone K (lowerBlock w)) := by sorry

end RobinsonSR.Schur

