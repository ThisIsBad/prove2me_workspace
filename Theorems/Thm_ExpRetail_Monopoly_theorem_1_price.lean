import Mathlib
import Definitions.Def_ExpRetail_Monopoly_Model

namespace ExpRetail.Monopoly

theorem theorem_1_price (P : Params) (hP : P.Standing) :
    (∃ pN : ℝ, IsOptPriceN P pN) ∧
    (∀ pN : ℝ, IsOptPriceN P pN → optProfitN P = profitN P pN) ∧
    ∀ ux : ℝ, 0 ≤ ux →
      (∃ p : ℝ, IsOptPrice P ux p) ∧
      (∀ p : ℝ, IsOptPrice P ux p → optProfit P ux = profit P ux p) ∧
      ∀ p pN : ℝ, IsOptPrice P ux p → IsOptPriceN P pN → pN < p := by sorry

end ExpRetail.Monopoly

