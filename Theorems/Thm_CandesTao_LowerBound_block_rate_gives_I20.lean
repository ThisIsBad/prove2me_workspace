import Definitions.Def_CandesTao_LowerBound_SamplingConditions

namespace CandesTao.LowerBound

theorem block_rate_gives_I20
    (n m r : ℕ) (μ₀ δ : ℝ) (ℓ : ℕ)
    (hm : 1 ≤ m) (hr : 1 ≤ r) (hrn : r ≤ n) (hμ₀ : 1 ≤ μ₀)
    (hδ : 0 < δ) (hδ' : δ < 1 / 2)
    (hℓ : (ℓ : ℝ) = n / (μ₀ * r))
    (h : (1 - (m : ℝ) / (n : ℝ) ^ 2) ^ ℓ ≤ 2 * δ / n) :
    SamplingConditionI20 n m r μ₀ δ := by sorry

end CandesTao.LowerBound
