import Mathlib
import Definitions.Def_PreorderADI_Correlation_Model

open MeasureTheory ProbabilityTheory

namespace PreorderADI.Correlation

theorem newsvendor_order_and_profit (P : Params) (hP : P.Standing)
    (ρ : ℝ) (hρ : ρ ∈ Set.Ico (0:ℝ) 1) (x : ℝ) :
    (∀ Q : ℝ, expectedSecondProfit P ρ x Q ≤ expectedSecondProfit P ρ x (orderQty P ρ x)) ∧
    (∀ Q : ℝ, (∀ Q' : ℝ, expectedSecondProfit P ρ x Q' ≤ expectedSecondProfit P ρ x Q) →
      Q = orderQty P ρ x) ∧
    expectedSecondProfit P ρ x (orderQty P ρ x) = secondProfit P ρ x := by sorry

end PreorderADI.Correlation
