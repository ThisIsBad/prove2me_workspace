import Mathlib
import Definitions.Def_TotalVariationDist
import Definitions.Def_ChenStein_Process_Setting

namespace ChenStein.Process

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

theorem Ti_comp_Si {d : ℕ} (i : Fin d) (lj : ℝ≥0) (hlj : 0 < lj)
    (h : (Fin d → ℕ) → ℝ) :
    ∀ j, Ti i lj (Si i lj h) j = h j := by sorry

end ChenStein.Process

