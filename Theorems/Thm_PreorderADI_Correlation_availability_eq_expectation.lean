import Mathlib
import Definitions.Def_PreorderADI_Correlation_Model

open MeasureTheory ProbabilityTheory

namespace PreorderADI.Correlation

theorem availability_eq_expectation (P : Params) (hP : P.Standing)
    (ρ : ℝ) (hρ : ρ ∈ Set.Ico (0:ℝ) 1) :
    (∀ x : ℝ, (lowDemandLaw P ρ x).real {y | y / 2 < orderQty P ρ x} =
      stdNormalCdf ((P.lamL + ρ * x) / Real.sqrt (1 - ρ ^ 2) + 2 * P.zL)) ∧
    availability P ρ =
      ∫ x, stdNormalCdf ((P.lamL + ρ * x) / Real.sqrt (1 - ρ ^ 2) + 2 * P.zL)
        ∂(gaussianReal 0 1) := by sorry

end PreorderADI.Correlation
