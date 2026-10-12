import Mathlib
import Definitions.Def_WhitinPrice_StyleGoods_Model

namespace WhitinPrice.StyleGoods
theorem eq_14_optimal_expected_profit (k P₀ L P : ℝ) (hk : k < 0) (hL : 0 < L) (hP : 0 < P)
    (hPP₀ : P < P₀) :
    expectedProfit k P₀ L P (optimalStock k P₀ L P) = -(k * P ^ 2 * (P₀ - P)) / (P + L) := by sorry
end WhitinPrice.StyleGoods

