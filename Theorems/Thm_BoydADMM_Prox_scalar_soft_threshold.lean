import Mathlib
import Definitions.Def_BoydADMM_Prox_Basic

open Matrix

namespace BoydADMM.Prox

theorem scalar_soft_threshold (lam ρ : ℝ) (hlam : 0 < lam) (hρ : 0 < ρ) (a t : ℝ) :
    (∀ s : ℝ, lam * |t| + (ρ / 2) * (t - a) ^ 2 ≤ lam * |s| + (ρ / 2) * (s - a) ^ 2) ↔
      t = softThreshold (lam / ρ) a := by sorry

end BoydADMM.Prox

