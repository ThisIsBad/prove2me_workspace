import Mathlib
import Definitions.Def_BoydADMM_ModelFit_Basic

open Matrix

namespace BoydADMM.ModelFit

/-- §8.3, p. 68: in the feature-split ADMM, the `z`-update over `(z₁, …, z_N)` reduces to the
`z̄`-update for the average `z̄` plus the explicit formula for each `zᵢ`, and then all the scaled
dual variables `uᵢ^{k+1} = uᵢ^k + Aᵢxᵢ^{k+1} − zᵢ^{k+1}` equal `Ax̄^{k+1} + ū^k − z̄^{k+1}`. -/
theorem feature_split_duals_agree {N m : ℕ} {n : Fin N → ℕ} (hN : 0 < N)
    (A : ∀ i, Matrix (Fin m) (Fin (n i)) ℝ) (l : EuclideanSpace ℝ (Fin m) → ℝ)
    (hl : ConvexOn ℝ Set.univ l) (b : EuclideanSpace ℝ (Fin m)) (ρ : ℝ) (hρ : 0 < ρ)
    (x : ∀ i, EuclideanSpace ℝ (Fin (n i))) (u z u' : Fin N → EuclideanSpace ℝ (Fin m))
    (hu' : ∀ i, u' i = u i + Matrix.toEuclideanLin (A i) (x i) - z i) :
    (IsMinOn (fun z' : Fin N → EuclideanSpace ℝ (Fin m) =>
        l ((∑ i, z' i) - b) + ∑ i, ρ / 2 * ‖Matrix.toEuclideanLin (A i) (x i) - z' i + u i‖ ^ 2)
        Set.univ z ↔
      (IsMinOn (fun zb : EuclideanSpace ℝ (Fin m) =>
          l ((N : ℝ) • zb - b) + (N : ℝ) * ρ / 2 *
            ‖zb - (N : ℝ)⁻¹ • (∑ i, Matrix.toEuclideanLin (A i) (x i))
              - (N : ℝ)⁻¹ • (∑ i, u i)‖ ^ 2)
          Set.univ ((N : ℝ)⁻¹ • (∑ i, z i)) ∧
        ∀ i, z i = (N : ℝ)⁻¹ • (∑ j, z j) + Matrix.toEuclideanLin (A i) (x i) + u i
          - (N : ℝ)⁻¹ • (∑ j, Matrix.toEuclideanLin (A j) (x j))
          - (N : ℝ)⁻¹ • (∑ j, u j))) ∧
    (IsMinOn (fun z' : Fin N → EuclideanSpace ℝ (Fin m) =>
        l ((∑ i, z' i) - b) + ∑ i, ρ / 2 * ‖Matrix.toEuclideanLin (A i) (x i) - z' i + u i‖ ^ 2)
        Set.univ z →
      ∀ i, u' i = (N : ℝ)⁻¹ • (∑ j, Matrix.toEuclideanLin (A j) (x j))
        + (N : ℝ)⁻¹ • (∑ j, u j) - (N : ℝ)⁻¹ • (∑ j, z j)) := by sorry

end BoydADMM.ModelFit

