import Mathlib
import Definitions.Def_CHMSPricing_SpmMatroid_Mechanism

namespace CHMSPricing.SpmMatroid

/-- Lemma 2, regular part (p. 5): if every `Fᵢ` is regular, the revenue of any truthful
mechanism `M` is at most `∑ᵢ p^M_i q^M_i`, where `q^M_i` is the probability that `M` serves `i`
and `p^M_i = Fᵢ⁻¹(1 − q^M_i)` (the price in `[loᵢ, hiᵢ]` with `Fᵢ(p^M_i) = 1 − q^M_i`). -/
theorem revenue_le_sum_price_mul_servProb {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : ι → ValueDist) (hreg : ∀ i, (D i).Regular)
    (J : SetSystem ι) (M : Mechanism ι) (hM : IsTruthful D J M)
    (p : ι → ℝ)
    (hp : ∀ i, p i ∈ Set.Icc (D i).lo (D i).hi ∧ (D i).cdf (p i) = 1 - servProb D M i) :
    revenue D M ≤ ∑ i, p i * servProb D M i := by sorry

end CHMSPricing.SpmMatroid

