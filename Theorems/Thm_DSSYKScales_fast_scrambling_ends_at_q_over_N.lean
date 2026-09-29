import Mathlib
import Definitions.Def_DSSYKScales_defs

open Filter Topology

namespace DSSYKScales
theorem fast_scrambling_ends_at_q_over_N (N q : ℕ → ℕ) (lam J : ℝ) (hJ : 0 < J)
    (hlim : IsDoubleScaledLimit N q lam) :
    Tendsto (fun n => (N n : ℝ) / (q n : ℝ) *
        scramblingProbability (N n) (q n) J (Real.log (q n : ℝ) / ((q n : ℝ) * J)))
      atTop (𝓝 (Real.log (1 + lam) / lam)) := by sorry
end DSSYKScales
