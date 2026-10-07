import Mathlib
import Definitions.Def_TalagrandConc_OnePoint_Basic

open MeasureTheory
open scoped ENNReal

namespace TalagrandConc.OnePoint

theorem lemma_2_2_2 (α t : ℝ) (hα : 0 < α) (ht : 0 ≤ t) :
    aAlpha α t ≤ Real.exp (t ^ 2 / 8 * (1 + 1 / α)) := by sorry

end TalagrandConc.OnePoint

