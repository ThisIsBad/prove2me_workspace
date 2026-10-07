import Mathlib
import Definitions.Def_MechanismDesign_DominantExamples_Auction

namespace MechanismDesign.DominantExamples

/-- Proposition 4.3, p.81. A dominant strategy incentive-compatible direct auction mechanism
is ex post individually rational if and only if for every buyer `i` and every
`θ_{-i} ∈ Θ_{-i}`: `t_i(θ̲, θ_{-i}) ≤ θ̲ q_i(θ̲, θ_{-i})`. -/
theorem auction_epir_iff {ι : Type*} [Fintype ι] [DecidableEq ι] {E : AuctionSetting}
    (M : AuctionMechanism E ι) (hM : M.IsDSIC) :
    M.IsEPIR ↔ ∀ i, ∀ θ ∈ E.typeSpace ι,
      M.t i (Function.update θ i E.lo) ≤ E.lo * M.q i (Function.update θ i E.lo) := by sorry

end MechanismDesign.DominantExamples

