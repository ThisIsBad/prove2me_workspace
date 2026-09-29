import Mathlib
import Definitions.Def_dS3_microstates

open Complex

namespace DS3Micro
theorem first_zero (b : ℂ) (hb : InRegime b) :
    (E0 b).im = 0 ∧ 2 < (E0 b).re ∧ rho0 b (E0 b).re = 0 ∧
      ∀ E : ℝ, 2 < E → E < (E0 b).re → (rho0 b E).im = 0 ∧ 0 < (rho0 b E).re := by
  sorry
end DS3Micro
