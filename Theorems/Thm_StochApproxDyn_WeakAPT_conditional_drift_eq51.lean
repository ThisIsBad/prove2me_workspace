import Mathlib
import Definitions.Def_StochApproxDyn_WeakAPT_WeakAsymptoticPseudotrajectory
import Definitions.Def_StochApproxDyn_WeakAPT_BlockIntegral

namespace StochApproxDyn.WeakAPT

open MeasureTheory Filter Topology
open scoped NNReal

/-- Benaïm (1999), §10, proof of Theorem 10.1, Eq. (51), p. 62: if `X` is a weak asymptotic
pseudotrajectory of `Φ`, `f : M → [0, 1]` is uniformly continuous and `T > 0`, then almost surely
`E(U_{i+1}(f,T) - U_i(f ∘ Φ_T, T) | 𝓕_{(i-1)T}) → 0` as `i → ∞`. -/
theorem conditional_drift_eq51
    {Ω M : Type*} {m0 : MeasurableSpace Ω} [MetricSpace M] [TopologicalSpace.SeparableSpace M]
    [MeasurableSpace M] [BorelSpace M]
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℝ≥0 m0)
    (Φ : Flow ℝ≥0 M) (X : ℝ≥0 → Ω → M)
    (hX : IsWeakAsymptoticPseudotrajectory P ℱ Φ X)
    (f : M → ℝ) (hf : UniformContinuous f) (hf01 : ∀ y, f y ∈ Set.Icc (0 : ℝ) 1)
    (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ ω ∂P, Tendsto
      (fun i : ℕ => (P[blockIntegral X f T (i + 1) - blockIntegral X (f ∘ Φ T) T i |
        ℱ (((i - 1 : ℕ) : ℝ≥0) * T)]) ω)
      atTop (𝓝 0) := by sorry

end StochApproxDyn.WeakAPT

