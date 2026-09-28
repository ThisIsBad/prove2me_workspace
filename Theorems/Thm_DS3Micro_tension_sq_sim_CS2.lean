import Mathlib
import Definitions.Def_dS3_microstates

open Complex

namespace DS3Micro
theorem tension_sq_sim_CS2 :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ b : ℂ, InRegime b → CS2 b = c * tensionHat b ^ 2 := by
  sorry
end DS3Micro
