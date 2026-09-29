import Mathlib
import Definitions.Def_PreorderADI_Correlation_Model

open MeasureTheory ProbabilityTheory

namespace PreorderADI.Correlation

theorem threshold_quasiconvex (P : Params) (hP : P.Standing)
    (hz : P.zL ≤ -(P.lamL / 2)) :
    QuasiconvexOn ℝ (Set.Ico (0:ℝ) 1) (threshold P) := by sorry

end PreorderADI.Correlation
