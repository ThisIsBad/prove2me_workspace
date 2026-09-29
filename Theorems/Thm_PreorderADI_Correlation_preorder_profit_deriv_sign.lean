import Mathlib
import Definitions.Def_PreorderADI_Correlation_Model

open MeasureTheory ProbabilityTheory

namespace PreorderADI.Correlation

theorem preorder_profit_deriv_sign (P : Params) (hP : P.Standing)
    (h2c : P.vL < 2 * P.c) (ρ : ℝ) (hρ : ρ ∈ Set.Ioo (0:ℝ) 1) :
    ∃ d : ℝ, HasDerivAt (preorderProfit P) d ρ ∧
      (0 < d ↔ P.muH < threshold P ρ) ∧ (d < 0 ↔ threshold P ρ < P.muH) := by sorry

end PreorderADI.Correlation
