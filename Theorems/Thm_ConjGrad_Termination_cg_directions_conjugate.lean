import Mathlib
import Definitions.Def_ConjGrad_Termination_cgIter

open Matrix

namespace ConjGrad.Termination

/-- Theorem 5:1, eq. (5:3b) (Hestenes–Stiefel 1952, p. 414). For a symmetric positive
definite `A`, the directions `p₀, p₁, …` of the cg-method (3:1) are mutually conjugate:
`(pᵢ, Apⱼ) = 0` for `i ≠ j`. -/
theorem cg_directions_conjugate {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (k x₀ : Fin n → ℝ) :
    ∀ i j, i ≠ j → (cgIter A k x₀ i).p ⬝ᵥ (A *ᵥ (cgIter A k x₀ j).p) = 0 := by sorry

end ConjGrad.Termination
