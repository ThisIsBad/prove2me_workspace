import Mathlib
import Definitions.Def_StochApproxDyn_WeakAPT_WeakAsymptoticPseudotrajectory
import Definitions.Def_StochApproxDyn_WeakAPT_BlockIntegral

namespace StochApproxDyn.WeakAPT

open MeasureTheory Filter Topology
open scoped NNReal

/-- Benaïm (1999), §10, proof of Theorem 10.1, Eq. (47), p. 62: for a progressively measurable
process `X`, a continuous `f : M → [0, 1]` and `T > 0`, almost surely
`(1/n) ∑_{i=1}^n [U_i(f,T) - E(U_i(f,T) | 𝓕_{(i-1)T})] → 0`. -/
theorem martingale_slln_eq47
    {Ω M : Type*} {m0 : MeasurableSpace Ω} [MetricSpace M] [TopologicalSpace.SeparableSpace M]
    [MeasurableSpace M] [BorelSpace M]
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℝ≥0 m0) (X : ℝ≥0 → Ω → M)
    (hX : IsProgressivelyMeasurable ℱ X)
    (f : M → ℝ) (hf : Continuous f) (hf01 : ∀ y, f y ∈ Set.Icc (0 : ℝ) 1)
    (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ ω ∂P, Tendsto
      (fun n : ℕ => (1 / (n : ℝ)) * ∑ i ∈ Finset.Icc 1 n,
        (blockIntegral X f T i ω - (P[blockIntegral X f T i | ℱ (((i - 1 : ℕ) : ℝ≥0) * T)]) ω))
      atTop (𝓝 0) := by sorry

end StochApproxDyn.WeakAPT

