import Mathlib
import Definitions.Def_dS3_microstates

open Complex

namespace DS3Micro
theorem Neff_closed_form (b : ℂ) (hb : InRegime b) (S0 : ℝ) :
    Neff b S0 = (Real.exp S0 : ℂ) *
      (-4 * Complex.I * Complex.sin ((Real.pi : ℂ) * b ^ 2) *
          Complex.sin ((Real.pi : ℂ) * (b ^ 2)⁻¹) /
        ((Real.pi : ℂ) * ((b ^ 2)⁻¹ - b ^ 2))) := by
  sorry
end DS3Micro
