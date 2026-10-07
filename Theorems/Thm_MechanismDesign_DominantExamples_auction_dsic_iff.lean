import Mathlib
import Definitions.Def_MechanismDesign_DominantExamples_Auction

namespace MechanismDesign.DominantExamples

/-- Proposition 4.2, p.81. A direct auction mechanism `(q, t_1, …, t_N)` is dominant strategy
incentive-compatible if and only if for every buyer `i` and every `θ_{-i} ∈ Θ_{-i}`
(represented by `θ ∈ Θ`, whose `i`-th coordinate is overwritten):
(i) `q_i(θ_i, θ_{-i})` is (weakly) increasing in `θ_i` on `[θ̲, θ̄]`;
(ii) for every `θ_i ∈ [θ̲, θ̄]`,
`t_i(θ_i, θ_{-i}) = t_i(θ̲, θ_{-i}) + (θ_i q_i(θ_i, θ_{-i}) − θ̲ q_i(θ̲, θ_{-i}))
  − ∫_{θ̲}^{θ_i} q_i(x, θ_{-i}) dx`. -/
theorem auction_dsic_iff {ι : Type*} [Fintype ι] [DecidableEq ι] {E : AuctionSetting}
    (M : AuctionMechanism E ι) :
    M.IsDSIC ↔ ∀ i, ∀ θ ∈ E.typeSpace ι,
      MonotoneOn (fun x => M.q i (Function.update θ i x)) (Set.Icc E.lo E.hi) ∧
      ∀ x ∈ Set.Icc E.lo E.hi,
        M.t i (Function.update θ i x) =
          M.t i (Function.update θ i E.lo)
            + (x * M.q i (Function.update θ i x) - E.lo * M.q i (Function.update θ i E.lo))
            - ∫ y in E.lo..x, M.q i (Function.update θ i y) := by sorry

end MechanismDesign.DominantExamples

