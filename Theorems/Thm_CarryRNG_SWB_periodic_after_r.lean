import Definitions.Def_CarryRNG_SWB_step

namespace CarryRNG.SWB

/-- Page 472: the orbit is strictly periodic after at most `r` steps. -/
theorem periodic_after_r (b : ℕ) (L : CarryRNG.AWC.Lags) (hb : 2 ≤ b) (z : CarryRNG.AWC.State b L.r) :
    (step b L hb)^[L.r] z ∈ Function.periodicPts (step b L hb) := by sorry

end CarryRNG.SWB

