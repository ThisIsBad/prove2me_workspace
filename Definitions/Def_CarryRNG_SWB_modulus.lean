import Definitions.Def_CarryRNG_AWC_Lags

namespace CarryRNG.SWB

/-- The modulus `b^r - b^s + 1` of the first subtract-with-borrow method. -/
def modulus (b : ℕ) (L : CarryRNG.AWC.Lags) : ℕ := b ^ L.r - b ^ L.s + 1

end CarryRNG.SWB
