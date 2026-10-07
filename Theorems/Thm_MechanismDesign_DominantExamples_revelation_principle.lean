import Mathlib
import Definitions.Def_MechanismDesign_DominantExamples_Auction

namespace MechanismDesign.DominantExamples

/-- Proposition 4.1 (Revelation Principle for Dominant Strategy Mechanisms), pp.79–80.
A general mechanism is given by message sets `S i`, one per buyer, and an outcome function
assigning to every message profile `s` the probabilities `alloc i s` with which buyer `i` gets
the good (a point of `Δ`) and the expected payments `pay i s`. The strategy `σ i` maps every
type of buyer `i` to a message, and `σ i θ_i` is dominant: it is optimal for type `θ_i` against
every message profile of the other buyers. Then there is a direct mechanism in which truth
telling is dominant (dominant strategy incentive compatibility) and which yields, at every type
vector, the same allocation probabilities and the same expected payments as `σ` in the
original mechanism. -/
theorem revelation_principle {ι : Type*} [Fintype ι] [DecidableEq ι] (E : AuctionSetting)
    {S : ι → Type*} (alloc pay : ι → ((j : ι) → S j) → ℝ)
    (h_alloc_nonneg : ∀ s i, 0 ≤ alloc i s) (h_alloc_le_one : ∀ s i, alloc i s ≤ 1)
    (h_alloc_sum : ∀ s, ∑ i, alloc i s ≤ 1)
    (σ : (i : ι) → ℝ → S i)
    (h_dominant : ∀ i, ∀ x ∈ Set.Icc E.lo E.hi, ∀ s : (j : ι) → S j, ∀ s' : S i,
      x * alloc i (Function.update s i s') - pay i (Function.update s i s') ≤
        x * alloc i (Function.update s i (σ i x)) - pay i (Function.update s i (σ i x))) :
    ∃ M : AuctionMechanism E ι, M.IsDSIC ∧
      ∀ θ ∈ E.typeSpace ι, ∀ i,
        M.q i θ = alloc i (fun j => σ j (θ j)) ∧ M.t i θ = pay i (fun j => σ j (θ j)) := by sorry

end MechanismDesign.DominantExamples

