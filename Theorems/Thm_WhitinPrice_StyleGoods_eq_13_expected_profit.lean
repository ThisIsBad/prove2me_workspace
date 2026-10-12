import Mathlib
import Definitions.Def_WhitinPrice_StyleGoods_Model

namespace WhitinPrice.StyleGoods
theorem eq_13_expected_profit (k P₀ L P x : ℝ) (hk : k < 0) (hL : 0 < L) (hP : 0 < P)
    (hPP₀ : P < P₀) (hx₀ : 0 ≤ x) (hx : x ≤ 2 * meanDemand k P₀ P) :
    expectedProfit k P₀ L P x = (P + L) / (4 * k * (P₀ - P)) * x ^ 2 + P * x := by sorry
end WhitinPrice.StyleGoods

