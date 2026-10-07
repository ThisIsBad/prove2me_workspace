import Mathlib
import Definitions.Def_BoydADMM_ModelFit_Basic

open Matrix

namespace BoydADMM.ModelFit

/-- §8.3.4, pp. 70–71: the feature-split SVM `z̄`-update
`argmin_{z̄} (1ᵀ(N z̄ + 1)₊ + (ρ/2)‖z̄ − Ax̄ − u‖₂²)` is the shifted soft thresholding of
`v = Ax̄ + u`, componentwise. -/
theorem svm_zbar_shifted_soft_threshold {N m : ℕ} (hN : 0 < N) (ρ : ℝ) (hρ : 0 < ρ)
    (Axbar u zb : EuclideanSpace ℝ (Fin m)) :
    IsMinOn (fun z : EuclideanSpace ℝ (Fin m) =>
        (∑ j, max ((N : ℝ) * z j + 1) 0) + ρ / 2 * ‖z - Axbar - u‖ ^ 2) Set.univ zb ↔
      ∀ j, zb j = shiftedSoftThreshold N ρ (Axbar j + u j) := by sorry

end BoydADMM.ModelFit

