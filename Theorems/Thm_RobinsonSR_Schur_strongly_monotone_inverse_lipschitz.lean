import Mathlib
import Definitions.Def_RobinsonSR_Schur_Setting

namespace RobinsonSR.Schur

/-- Robinson, p. 52, the inverse of the reduced operator. -/
theorem strongly_monotone_inverse_lipschitz (r s : ℕ) (hr : 0 < r) (hs : 0 < s)
    (A₁₁ : Matrix (Fin r) (Fin r) ℝ)
    (A₁₂ : Matrix (Fin r) (Fin s) ℝ)
    (A₂₁ : Matrix (Fin s) (Fin r) ℝ)
    (A₂₂ : Matrix (Fin s) (Fin s) ℝ)
    (hA₁₁ : A₁₁.det ≠ 0)
    (K : Set (EuclideanSpace ℝ (Fin s)))
    (hK₁ : K.Nonempty) (hK₂ : IsClosed K) (hK₃ : Convex ℝ K)
    (hM : PosDefNS (schur A₁₁ A₁₂ A₂₁ A₂₂)) :
    InvIsLipschitzFunction (schur A₁₁ A₁₂ A₂₁ A₂₂) K := by sorry

end RobinsonSR.Schur

