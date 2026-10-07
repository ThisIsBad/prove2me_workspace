import Mathlib
import Definitions.Def_BoydADMM_ModelFit_Basic

open Matrix

namespace BoydADMM.ModelFit

/-- §8.2.1, p. 65: the distributed-lasso `z`-update
`argmin_z (λ‖z‖₁ + (Nρ/2)‖z − x̄ − ū‖₂²)` is soft thresholding `S_{λ/(ρN)}(x̄ + ū)`, componentwise. -/
theorem lasso_z_update_soft_threshold {N n : ℕ} (hN : 0 < N)
    (x u : Fin N → EuclideanSpace ℝ (Fin n)) (lam ρ : ℝ) (hlam : 0 < lam) (hρ : 0 < ρ)
    (z : EuclideanSpace ℝ (Fin n)) :
    IsMinOn (fun z' : EuclideanSpace ℝ (Fin n) =>
        lam * l1norm z' + (N : ℝ) * ρ / 2 *
          ‖z' - (N : ℝ)⁻¹ • (∑ i, x i) - (N : ℝ)⁻¹ • (∑ i, u i)‖ ^ 2) Set.univ z ↔
      ∀ j, z j = BoydADMM.Prox.softThreshold (lam / (ρ * N))
        (((N : ℝ)⁻¹ • (∑ i, x i)) j + ((N : ℝ)⁻¹ • (∑ i, u i)) j) := by sorry

end BoydADMM.ModelFit

