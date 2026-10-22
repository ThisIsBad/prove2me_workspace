import Definitions.Def_CarryRNG_AWC_State

namespace CarryRNG.SWB

/-- The integer with base-`b` representation `x_(r-s) ... x_1`. -/
def lowBlock (b : ℕ) (L : CarryRNG.AWC.Lags) (z : CarryRNG.AWC.State b L.r) : ℕ :=
  ∑ i : Fin (L.r - L.s), (z.x ⟨i.val, by have := L.hsr; have := i.isLt; omega⟩).val * b ^ i.val

end CarryRNG.SWB
