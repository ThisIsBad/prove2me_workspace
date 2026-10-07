import Mathlib
import Definitions.Def_CachonCoord_Proportional_Demand
import Definitions.Def_CachonCoord_Proportional_Nash
import Definitions.Def_CachonCoord_Proportional_Game

namespace CachonCoord.Proportional

open Filter Topology

/-- p. 51, Eq. (22): "The left hand side of (22) is increasing in `q*` from 0 (when `q* = 0`)
to 1 (when `q* = ∞`). Hence, when `b < w < p`, there exists a unique `q*` that satisfies (22)."
Here `L_n(q) = (1/n) F(q) + ((n − 1)/n) (1/q) ∫_0^q F` is strictly increasing on `q > 0`, tends to
`0` as `q → 0⁺` and to `1` as `q → ∞`, and `L_n(q*) = (p − w)/(p − b)` has exactly one root
`q* > 0`. -/
theorem eq_22_root (M : Model) (n : ℕ) (hn : 2 ≤ n) :
    StrictMonoOn (M.lhs22 n) (Set.Ioi 0) ∧
      Tendsto (M.lhs22 n) (𝓝[>] 0) (𝓝 0) ∧
      Tendsto (M.lhs22 n) atTop (𝓝 1) ∧
      ∀ w b : ℝ, b < w → w < M.p →
        ∃! qs : ℝ, 0 < qs ∧ M.lhs22 n qs = (M.p - w) / (M.p - b) := by sorry

end CachonCoord.Proportional

