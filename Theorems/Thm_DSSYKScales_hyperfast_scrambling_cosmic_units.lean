import Mathlib
import Definitions.Def_DSSYKScales_defs

open Filter Topology

namespace DSSYKScales
theorem hyperfast_scrambling_cosmic_units (N q : ℕ → ℕ) (lam J : ℝ) (hJ : 0 < J)
    (hlim : IsDoubleScaledLimit N q lam) (tc : ℝ) (htc : 0 < tc) :
    Tendsto (fun n => 1 - scramblingProbability (N n) (q n) J tc)
      atTop (𝓝 (Real.exp (-(J * tc)))) := by sorry
end DSSYKScales
