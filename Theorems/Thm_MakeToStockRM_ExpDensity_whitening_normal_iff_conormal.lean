import Mathlib
import Definitions.Def_MakeToStockRM_ExpDensity_covMatrix

namespace MakeToStockRM.ExpDensity

open Matrix

theorem whitening_normal_iff_conormal (σ δ ϱ : ℝ) (hσ : 0 < σ) (hδ : 0 < δ) (hϱ : |ϱ| < 1)
    (V : Matrix (Fin 2) (Fin 2) ℝ) (e : Fin 2 → ℝ)
    (hV : V * V.transpose = 1) (hVdet : V.det = 1) (he : ∀ i, 0 < e i)
    (hSigma : covMatrix σ δ ϱ = V.transpose * Matrix.diagonal e * V) :
    (∀ v w : Fin 2 → ℝ,
      ((Matrix.diagonal (fun i => (Real.sqrt (e i))⁻¹) * V) *ᵥ v)
          ⬝ᵥ ((Matrix.diagonal (fun i => (Real.sqrt (e i))⁻¹) * V) *ᵥ w)
        = v ⬝ᵥ ((covMatrix σ δ ϱ)⁻¹ *ᵥ w)) ∧
    (∀ n v : Fin 2 → ℝ, n ≠ 0 →
      ((∀ w : Fin 2 → ℝ, n ⬝ᵥ w = 0 →
          ((Matrix.diagonal (fun i => (Real.sqrt (e i))⁻¹) * V) *ᵥ v)
            ⬝ᵥ ((Matrix.diagonal (fun i => (Real.sqrt (e i))⁻¹) * V) *ᵥ w) = 0)
        ↔ ∃ c : ℝ, v = c • (covMatrix σ δ ϱ *ᵥ n))) := by sorry

end MakeToStockRM.ExpDensity
