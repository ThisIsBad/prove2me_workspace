import Mathlib
import Definitions.Def_WhitinPrice_StyleGoods_Model

namespace WhitinPrice.StyleGoods
theorem optimal_unit_profit (k P₀ L Pstar : ℝ) (hk : k < 0) (hL : 0 < L) (hP₀ : 0 < P₀)
    (hPstar : Pstar = ((P₀ - 3 * L) + Real.sqrt ((3 * L - P₀) ^ 2 + 16 * P₀ * L)) / 4) :
    0 < Pstar ∧ Pstar < P₀ ∧
      (∀ P x : ℝ, 0 < P → P < P₀ → 0 ≤ x →
        expectedProfit k P₀ L P x ≤ expectedProfit k P₀ L Pstar (optimalStock k P₀ L Pstar)) ∧
      (∀ P x : ℝ, 0 < P → P < P₀ → 0 ≤ x →
        expectedProfit k P₀ L P x = expectedProfit k P₀ L Pstar (optimalStock k P₀ L Pstar) →
          P = Pstar ∧ x = optimalStock k P₀ L Pstar) := by sorry
end WhitinPrice.StyleGoods

