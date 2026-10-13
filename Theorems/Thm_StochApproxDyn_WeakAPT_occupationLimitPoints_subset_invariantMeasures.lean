import Mathlib
import Definitions.Def_StochApproxDyn_WeakAPT_InvariantMeasures
import Definitions.Def_StochApproxDyn_WeakAPT_OccupationMeasure
import Definitions.Def_StochApproxDyn_WeakAPT_WeakAsymptoticPseudotrajectory

namespace StochApproxDyn.WeakAPT

open MeasureTheory Filter Topology
open scoped NNReal

/-- Benaïm (1999), Theorem 10.1, p. 61: if `X` is a weak asymptotic pseudotrajectory of the
semiflow `Φ` on a separable metric space `M`, then for `P`-almost every `ω` every weak limit point
of the occupation measures `μ_t(ω)` is `Φ`-invariant: `𝓜(X, ω) ⊂ 𝓜(Φ)`. -/
theorem occupationLimitPoints_subset_invariantMeasures
    {Ω M : Type*} {m0 : MeasurableSpace Ω} [MetricSpace M] [TopologicalSpace.SeparableSpace M]
    [MeasurableSpace M] [BorelSpace M]
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℝ≥0 m0)
    (Φ : Flow ℝ≥0 M) (X : ℝ≥0 → Ω → M)
    (hX : IsWeakAsymptoticPseudotrajectory P ℱ Φ X) :
    ∀ᵐ ω ∂P, occupationLimitPoints X ω ⊆ invariantMeasures Φ := by sorry

end StochApproxDyn.WeakAPT

