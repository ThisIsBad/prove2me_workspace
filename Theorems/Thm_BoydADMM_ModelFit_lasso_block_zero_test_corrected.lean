import Mathlib
import Definitions.Def_BoydADMM_ModelFit_Basic

open Matrix

namespace BoydADMM.ModelFit

/-- §8.3.1, p. 69, corrected: `0` minimizes `(ρ/2)‖Aᵢxᵢ − v‖₂² + λ‖xᵢ‖₁` iff
`‖Aᵢᵀv‖_∞ ≤ λ/ρ` (the book prints `‖·‖₂`, which is false for the ℓ1 block term). -/
theorem lasso_block_zero_test_corrected {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (v : EuclideanSpace ℝ (Fin m)) (ρ lam : ℝ) (hρ : 0 < ρ) (hlam : 0 < lam) :
    IsMinOn (fun x : EuclideanSpace ℝ (Fin n) =>
        ρ / 2 * ‖Matrix.toEuclideanLin A x - v‖ ^ 2 + lam * l1norm x) Set.univ 0 ↔
      ∀ j, |Matrix.toEuclideanLin Aᵀ v j| ≤ lam / ρ := by sorry

end BoydADMM.ModelFit

