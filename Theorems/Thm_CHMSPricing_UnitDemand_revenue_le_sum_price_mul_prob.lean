import Mathlib
import Definitions.Def_CHMSPricing_UnitDemand_Mechanism

namespace CHMSPricing.UnitDemand

/-- Lemma 2 (regular part), p. 5: if every `Fᵢ` is regular, the revenue of every truthful
mechanism `M` is at most `∑ᵢ p^M_i q^M_i`, where `q^M_i` is the probability that `M` serves
agent `i` and `p^M_i = Fᵢ⁻¹(1 − q^M_i)` (the point of the support with `Fᵢ(p^M_i) = 1 − q^M_i`). -/
theorem revenue_le_sum_price_mul_prob {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : ι → ValueDist) (hreg : ∀ i, (D i).Regular) (𝒥 : SetSystem ι)
    (M : Mechanism ι) (hM : IsTruthful D 𝒥 M) (pM : ι → ℝ)
    (hpM : ∀ i, pM i ∈ Set.Icc (D i).lo (D i).hi ∧ (D i).cdf (pM i) = 1 - servProb D M i) :
    revenue D M ≤ ∑ i, pM i * servProb D M i := by sorry

end CHMSPricing.UnitDemand

