import Definitions.Def_CarryRNG_AWC_State

namespace CarryRNG.SWB

/-- The integer with base-`b` representation `x_r ... x_(s+1)`. -/
def highBlock (b : ℕ) (L : CarryRNG.AWC.Lags) (z : CarryRNG.AWC.State b L.r) : ℕ :=
  ∑ i : Fin (L.r - L.s), (z.x ⟨L.s + i.val, by have := L.hsr; have := i.isLt; omega⟩).val * b ^ i.val

end CarryRNG.SWB
