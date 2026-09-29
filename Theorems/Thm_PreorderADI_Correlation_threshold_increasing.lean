import Mathlib
import Definitions.Def_PreorderADI_Correlation_Model

open MeasureTheory ProbabilityTheory

namespace PreorderADI.Correlation

theorem threshold_increasing (P : Params) (hP : P.Standing)
    (hz : -(P.lamL / 2) < P.zL) (hz0 : P.zL < 0) :
    StrictMonoOn (threshold P) (Set.Ico (0:ℝ) 1) := by sorry

end PreorderADI.Correlation
