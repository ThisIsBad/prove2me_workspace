import Definitions.Def_CandesTao_LowerBound_SamplingConditions

namespace CandesTao.LowerBound

theorem I20_implies_I21
    (n m r : ℕ) (μ₀ δ : ℝ)
    (hm : 1 ≤ m) (hr : 1 ≤ r) (hrn : r ≤ n) (hμ₀ : 1 ≤ μ₀)
    (hδ : 0 < δ) (hδ' : δ < 1 / 2)
    (h : SamplingConditionI20 n m r μ₀ δ) :
    SamplingConditionI21 n m r μ₀ δ := by sorry

end CandesTao.LowerBound
