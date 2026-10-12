import Mathlib
import Definitions.Def_WhitinPrice_StyleGoods_Model

namespace WhitinPrice.StyleGoods
theorem eq_15_stationary_quadratic (k P₀ L P : ℝ) (hk : k < 0) (hL : 0 < L) (hP : 0 < P)
    (hPP₀ : P < P₀) :
    HasDerivAt (fun Q : ℝ => expectedProfit k P₀ L Q (optimalStock k P₀ L Q))
        (k * P * (2 * P ^ 2 + (3 * L - P₀) * P - 2 * P₀ * L) / (P + L) ^ 2) P ∧
      (deriv (fun Q : ℝ => expectedProfit k P₀ L Q (optimalStock k P₀ L Q)) P = 0 ↔
        2 * P ^ 2 + (3 * L - P₀) * P - 2 * P₀ * L = 0) := by sorry
end WhitinPrice.StyleGoods

