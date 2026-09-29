import Mathlib
import Definitions.Def_PreorderADI_Correlation_Model

open MeasureTheory ProbabilityTheory

namespace PreorderADI.Correlation

theorem availability_decreasing_high_margin (P : Params) (hP : P.Standing)
    (h2c : 2 * P.c ≤ P.vL) :
    0 ≤ P.zL ∧ AntitoneOn (availability P) (Set.Ico (0:ℝ) 1) ∧
      (2 * P.c < P.vL → StrictAntiOn (availability P) (Set.Ico (0:ℝ) 1)) := by sorry

end PreorderADI.Correlation
