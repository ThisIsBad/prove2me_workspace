import Mathlib
import Definitions.Def_OnlinePrimalDual_AdAuctions_AdAuctionsInstance
import Definitions.Def_OnlinePrimalDual_AdAuctions_revenue

namespace OnlinePrimalDual.AdAuctions

/-- The actual revenue collected from buyer `i`: "the minimum between the sum of the bids of the
items allocated to a buyer... and the total budget of the buyer. That is, buyers can never be
charged by more than their total budget." (p. 211). -/
noncomputable def actualCharge {I M : Type*} [Fintype I] [Fintype M]
    (inst : AdAuctionsInstance I M) (wonBids : I → List ℝ) (i : I) : ℝ :=
  min (revenue inst wonBids i) (inst.B i)

end OnlinePrimalDual.AdAuctions
