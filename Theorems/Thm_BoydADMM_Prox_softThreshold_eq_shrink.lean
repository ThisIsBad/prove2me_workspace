import Mathlib
import Definitions.Def_BoydADMM_Prox_Basic

open Matrix

namespace BoydADMM.Prox

theorem softThreshold_eq_shrink (κ : ℝ) (hκ : 0 ≤ κ) (a : ℝ) (ha : a ≠ 0) :
    softThreshold κ a = max (1 - κ / |a|) 0 * a := by sorry

end BoydADMM.Prox

