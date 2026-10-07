import Mathlib
import Definitions.Def_BoydADMM_Prox_Basic

open Matrix

namespace BoydADMM.Prox

theorem prox_l1_eq_softThreshold {n : ℕ} (lam ρ : ℝ) (hlam : 0 < lam) (hρ : 0 < ρ)
    (v x : EuclideanSpace ℝ (Fin n)) :
    IsProx Set.univ (fun y => lam * l1Norm y) ρ v x ↔ x = softThresholdVec (lam / ρ) v := by sorry

end BoydADMM.Prox

