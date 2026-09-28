import Mathlib
import Definitions.Def_PreorderADI_Correlation_Model

open MeasureTheory ProbabilityTheory

namespace PreorderADI.Correlation

theorem second_profit_deriv (P : Params) (hP : P.Standing)
    (ρ : ℝ) (hρ : ρ ∈ Set.Ioo (0:ℝ) 1) :
    HasDerivAt (fun r => secondProfit P r 0)
      (P.vL * stdNormalPdf P.zL * P.sigmaL * (ρ / Real.sqrt (1 - ρ ^ 2))) ρ ∧
    0 < P.vL * stdNormalPdf P.zL * P.sigmaL * (ρ / Real.sqrt (1 - ρ ^ 2)) := by sorry

end PreorderADI.Correlation
