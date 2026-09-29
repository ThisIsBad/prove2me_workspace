import Mathlib
import Definitions.Def_CachonPushPull_Pareto_Model

namespace CachonPushPull.Pareto

open MeasureTheory ProbabilityTheory

/-- Lemma 1, p. 227: for `q > 0`, `j(q) h(q)` is (strictly) increasing. -/
theorem jh_strictMonoOn (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) :
    StrictMonoOn (fun q : ℝ => j μ q * hazard μ f q) (Set.Ioi 0) := by sorry

end CachonPushPull.Pareto
