import Mathlib
import Definitions.Def_OnlineStochMatching_Hardness_Model
import Definitions.Def_OnlineStochMatching_Hardness_SixCycle

namespace OnlineStochMatching.Hardness

/-- Theorem 3, first sentence (p. 4): on the 6-cycle instance (three advertisers, three
impression types, uniform arrivals, `n = 3`), every randomized online algorithm has expected
approximation factor `E[ALG/OPT]` at most `26/27`. -/
theorem theorem_3_single_cycle (P : PMF (OnlineAlg Adv Imp 3)) :
    randExpectedRatio cycleEdge P ≤ 26 / 27 := by sorry

end OnlineStochMatching.Hardness

