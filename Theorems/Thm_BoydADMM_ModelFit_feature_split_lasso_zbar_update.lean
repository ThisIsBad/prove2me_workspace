import Mathlib
import Definitions.Def_BoydADMM_ModelFit_Basic

open Matrix

namespace BoydADMM.ModelFit

/-- §8.3.1, p. 69: for the lasso loss `l(w) = (1/2)‖w‖₂²`, the feature-split `z̄`-update of p. 68
has the unique solution `z̄ = (b + ρ Ax̄ + ρ u)/(N + ρ)`. -/
theorem feature_split_lasso_zbar_update {N m : ℕ} (hN : 0 < N) (ρ : ℝ) (hρ : 0 < ρ)
    (b Axbar u zb : EuclideanSpace ℝ (Fin m)) :
    IsMinOn (fun z : EuclideanSpace ℝ (Fin m) =>
        1 / 2 * ‖(N : ℝ) • z - b‖ ^ 2 + (N : ℝ) * ρ / 2 * ‖z - Axbar - u‖ ^ 2) Set.univ zb ↔
      zb = (1 / ((N : ℝ) + ρ)) • (b + ρ • Axbar + ρ • u) := by sorry

end BoydADMM.ModelFit

