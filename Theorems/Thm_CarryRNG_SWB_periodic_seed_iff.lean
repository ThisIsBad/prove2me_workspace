import Definitions.Def_CarryRNG_SWB_step
import Definitions.Def_CarryRNG_SWB_highBlock
import Definitions.Def_CarryRNG_SWB_lowBlock
import Definitions.Def_CarryRNG_AWC_zeroSeed
import Definitions.Def_CarryRNG_AWC_topSeed

namespace CarryRNG.SWB

/-- Page 472, Method 1: the strict inequalities classify the nontrivial periodic seeds. -/
theorem periodic_seed_iff (b : ℕ) (L : CarryRNG.AWC.Lags) (hb : 2 ≤ b) (z : CarryRNG.AWC.State b L.r) :
    z ∈ Function.periodicPts (step b L hb) ↔
      (z.c.val = 0 ∧ highBlock b L z < lowBlock b L z) ∨
      (z.c.val = 1 ∧ lowBlock b L z < highBlock b L z) ∨
      z = CarryRNG.AWC.zeroSeed b L.r hb ∨ z = CarryRNG.AWC.topSeed b L.r hb := by sorry

end CarryRNG.SWB

