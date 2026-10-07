import Mathlib
import Definitions.Def_BoydADMM_ModelFit_Basic

open Matrix

namespace BoydADMM.ModelFit

/-- §8.3.2, p. 70: if `AᵢᵀAᵢ = Q diag(μ) Qᵀ` with `Q` orthogonal, then for `ν > 0`
`‖(AᵢᵀAᵢ + νI)⁻¹Aᵢᵀv‖₂ = ‖diag(μ + ν1)⁻¹ Qᵀ Aᵢᵀ v‖₂`. (The book's eigenvalue vector `λ` is `μ`.) -/
theorem group_lasso_eigen_norm {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (v : EuclideanSpace ℝ (Fin m)) (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Q ∈ Matrix.orthogonalGroup (Fin n) ℝ) (μ : Fin n → ℝ)
    (hdecomp : Aᵀ * A = Q * Matrix.diagonal μ * Qᵀ) (ν : ℝ) (hν : 0 < ν) :
    ‖ridgeSol A ν v‖ =
      ‖Matrix.toEuclideanLin ((Matrix.diagonal (fun j => μ j + ν))⁻¹ * Qᵀ * Aᵀ) v‖ := by sorry

end BoydADMM.ModelFit

