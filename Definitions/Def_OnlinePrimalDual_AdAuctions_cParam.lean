import Mathlib
import Definitions.Def_OnlinePrimalDual_AdAuctions_AdAuctionsInstance

namespace OnlinePrimalDual.AdAuctions

/-- The constant `c = (1 + Rmax)^(1/Rmax)` the Allocation algorithm's step (3) update rule is
parameterized by ("`c` is determined later", p. 212; fixed at this value in the proof of Claim
(3), p. 214: "This is why we set the value of `c` to be `(1+Rmax)^(1/Rmax)`"). `Real.rpow`
(the `ℝ → ℝ → ℝ` power, notation `^`) realizes the real exponent `1/Rmax`. -/
noncomputable def cParam {I M : Type*} [Fintype I] [Fintype M]
    (inst : AdAuctionsInstance I M) : ℝ :=
  (1 + inst.Rmax) ^ (1 / inst.Rmax)

end OnlinePrimalDual.AdAuctions
