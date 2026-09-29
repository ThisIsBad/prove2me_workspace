import Mathlib
import Definitions.Def_DSSYKScales_defs

open Filter Topology

namespace DSSYKScales
theorem fast_scrambling_string_units (N q : ℕ → ℕ) (lam J : ℝ)
    (hlim : IsDoubleScaledLimit N q lam) (ts : ℝ) :
    Tendsto (fun n => (N n : ℝ) * scramblingProbability (N n) (q n) J (ts / (q n : ℝ)))
      atTop (𝓝 (Real.exp (J * ts))) := by sorry
end DSSYKScales
