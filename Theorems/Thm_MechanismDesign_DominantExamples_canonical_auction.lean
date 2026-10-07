import Mathlib
import Definitions.Def_MechanismDesign_DominantExamples_Auction

namespace MechanismDesign.DominantExamples

/-- Proposition 4.4, p.83. Every canonical auction is dominant strategy incentive-compatible
and ex post individually rational. Moreover, for every buyer `i`, `u_i(θ̲, θ_{-i}) = 0` for all
`θ_{-i} ∈ Θ_{-i}`. -/
theorem canonical_auction {ι : Type*} [Fintype ι] [DecidableEq ι] {E : AuctionSetting}
    (M : AuctionMechanism E ι) (hM : M.IsCanonical) :
    M.IsDSIC ∧ M.IsEPIR ∧
      ∀ i, ∀ θ ∈ E.typeSpace ι, M.u i (Function.update θ i E.lo) = 0 := by sorry

end MechanismDesign.DominantExamples

