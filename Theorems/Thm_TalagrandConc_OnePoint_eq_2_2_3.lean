import Mathlib
import Definitions.Def_TalagrandConc_OnePoint_Basic

open MeasureTheory
open scoped ENNReal

namespace TalagrandConc.OnePoint

theorem eq_2_2_3 (α t : ℝ) (hα : 0 < α) (ht : 0 ≤ t) :
    aAlpha α t = sSup ((fun u : ℝ =>
      (1 + u * (Real.exp t - 1)) * (1 - u * (1 - Real.exp (-t / α))) ^ α) '' Set.Icc 0 1) := by sorry

end TalagrandConc.OnePoint

