import Mathlib
import Definitions.Def_StochApproxDyn_LimitSet_AsymptoticPseudotrajectory
import Definitions.Def_StochApproxDyn_LimitSet_TranslationSemiflow

open scoped NNReal

namespace StochApproxDyn.LimitSet

/-- Lemma 3.1 (Benaïm 1999, p. 10), on `C⁰(ℝ₊, M)`: a continuous `X : ℝ₊ → M` is an asymptotic
pseudotrajectory of `Φ` iff `d(Θ^t(X), Φ̂(Θ^t(X))) → 0` as `t → ∞`. -/
theorem isAsymptoticPseudotrajectory_iff_tendsto_retraction {M : Type*} [MetricSpace M]
    (Φ : Flow ℝ≥0 M) (X : C(ℝ≥0, M)) :
    IsAsymptoticPseudotrajectory Φ X ↔
      Filter.Tendsto
        (fun t : ℝ≥0 => uniformCompactDist (translate t X) (retraction Φ (translate t X)))
        Filter.atTop (nhds 0) := by sorry

end StochApproxDyn.LimitSet

