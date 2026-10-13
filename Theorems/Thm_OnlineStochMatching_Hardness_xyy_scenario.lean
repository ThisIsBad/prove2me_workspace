import Mathlib
import Definitions.Def_OnlineStochMatching_Hardness_Model
import Definitions.Def_OnlineStochMatching_Hardness_SixCycle

namespace OnlineStochMatching.Hardness

/-- §3, p. 4 (the "(x, y, y)" argument behind Theorem 3). On the 6-cycle with `n = 3` arrivals,
for every deterministic online algorithm and every type `u` of the first arrival there is a type
`v` such that on the scenario `(u, v, v)` the algorithm assigns at most two arrivals while the
optimum assigns all three. (The paper's case: `u = x` assigned to `a`, `v = y`.) -/
theorem xyy_scenario (alg : OnlineAlg Adv Imp 3) (u : Imp) :
    ∃ v : Imp, ALG cycleEdge alg ![u, v, v] ≤ 2 ∧ OPT cycleEdge ![u, v, v] = 3 := by sorry

end OnlineStochMatching.Hardness

