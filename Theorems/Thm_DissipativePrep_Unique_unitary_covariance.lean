import Mathlib
import Definitions.Def_DissipativePrep_Unique_Model

open scoped Matrix ComplexConjugate
open QAlgorithms QAlgorithms.Papers.Independent.Dependency50.P16

namespace DissipativePrep.Unique

theorem unitary_covariance {n : ℕ} (U : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) (g : Fin n → ℝ) (hg : ∀ k, 0 < g k) :
    (∀ σ : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ,
      gkslGenerator (prepData U g 0 Matrix.isHermitian_zero) σ =
        U * gkslGenerator (prepData 1 g 0 Matrix.isHermitian_zero) (Uᴴ * σ * U) * Uᴴ) ∧
    ∀ (σ : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) (μ : ℂ),
      gkslGenerator (prepData U g 0 Matrix.isHermitian_zero) σ = μ • σ ↔
        gkslGenerator (prepData 1 g 0 Matrix.isHermitian_zero) (Uᴴ * σ * U) = μ • (Uᴴ * σ * U) := by sorry

end DissipativePrep.Unique

