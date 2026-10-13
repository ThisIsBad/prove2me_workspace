import Mathlib
import Definitions.Def_StochApproxDyn_WeakAPT_WeakAsymptoticPseudotrajectory
import Definitions.Def_StochApproxDyn_WeakAPT_BlockIntegral

namespace StochApproxDyn.WeakAPT

open MeasureTheory Filter Topology
open scoped NNReal

/-- Benaïm (1999), §10, proof of Theorem 10.1, Eq. (52), p. 63: if `X` is a weak asymptotic
pseudotrajectory of `Φ`, `f : M → [0, 1]` is uniformly continuous and `T > 0`, then almost surely
`(1/n) ∑_{i=1}^n U_{i+1}(f,T) - (1/n) ∑_{i=1}^n U_i(f ∘ Φ_T, T) → 0`. -/
theorem block_average_difference_eq52
    {Ω M : Type*} {m0 : MeasurableSpace Ω} [MetricSpace M] [TopologicalSpace.SeparableSpace M]
    [MeasurableSpace M] [BorelSpace M]
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℝ≥0 m0)
    (Φ : Flow ℝ≥0 M) (X : ℝ≥0 → Ω → M)
    (hX : IsWeakAsymptoticPseudotrajectory P ℱ Φ X)
    (f : M → ℝ) (hf : UniformContinuous f) (hf01 : ∀ y, f y ∈ Set.Icc (0 : ℝ) 1)
    (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ ω ∂P, Tendsto
      (fun n : ℕ => (1 / (n : ℝ)) * ∑ i ∈ Finset.Icc 1 n, blockIntegral X f T (i + 1) ω -
        (1 / (n : ℝ)) * ∑ i ∈ Finset.Icc 1 n, blockIntegral X (f ∘ Φ T) T i ω)
      atTop (𝓝 0) := by sorry

end StochApproxDyn.WeakAPT

