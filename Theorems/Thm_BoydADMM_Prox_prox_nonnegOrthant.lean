import Mathlib
import Definitions.Def_BoydADMM_Prox_Basic

open Matrix

namespace BoydADMM.Prox

theorem prox_nonnegOrthant {n : ℕ} (ρ : ℝ) (hρ : 0 < ρ) (v : EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) :
    IsProx (nonnegOrthant n) (fun _ => 0) ρ v x ↔ x = posPartVec v := by sorry

end BoydADMM.Prox

