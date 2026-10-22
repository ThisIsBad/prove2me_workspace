import Definitions.Def_CarryRNG_SWB_step

namespace CarryRNG.SWB

/-- The one-based stream: seed digits first, then the new last CarryRNG.AWC.digit after each step. -/
def out (b : ℕ) (L : CarryRNG.AWC.Lags) (hb : 2 ≤ b) (z : CarryRNG.AWC.State b L.r) (n : ℕ) : ℕ :=
  if h : 1 ≤ n ∧ n ≤ L.r then (z.x ⟨n - 1, by omega⟩).val
  else (((step b L hb)^[n - L.r] z).x ⟨L.r - 1, by have := L.hsr; omega⟩).val

end CarryRNG.SWB
