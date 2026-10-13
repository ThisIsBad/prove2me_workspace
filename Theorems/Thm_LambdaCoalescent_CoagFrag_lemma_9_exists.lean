import Mathlib
import Definitions.Def_LambdaCoalescent_CoagFrag_Setting

namespace LambdaCoalescent.CoagFrag

open MeasureTheory

theorem lemma_9_exists (α θ : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1) (hθ : -α < θ) :
    ∃ μ : Measure LambdaCoalescent.Rates.PInf, IsProbabilityMeasure μ ∧ IsEPFLaw (pdEPF α θ) μ := by sorry

end LambdaCoalescent.CoagFrag

