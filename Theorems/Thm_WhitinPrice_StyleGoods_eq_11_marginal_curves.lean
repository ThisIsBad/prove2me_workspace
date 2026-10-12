import Mathlib
import Definitions.Def_WhitinPrice_StyleGoods_Model

namespace WhitinPrice.StyleGoods
theorem eq_11_marginal_curves (k P₀ L P x : ℝ) (hk : k < 0) (hL : 0 < L) (hP : 0 < P)
    (hPP₀ : P < P₀) (hx₀ : 0 ≤ x) (hx : x ≤ 2 * meanDemand k P₀ P) :
    marginalProfit k P₀ P x = P / (2 * k * (P₀ - P)) * x + P ∧
      marginalLoss k P₀ L P x = -L / (2 * k * (P₀ - P)) * x := by sorry
end WhitinPrice.StyleGoods

