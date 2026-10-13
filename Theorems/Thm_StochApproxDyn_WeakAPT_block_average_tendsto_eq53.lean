import Mathlib
import Definitions.Def_StochApproxDyn_WeakAPT_OccupationMeasure

namespace StochApproxDyn.WeakAPT

open MeasureTheory Filter Topology
open scoped NNReal

/-- Benaïm (1999), §10, proof of Theorem 10.1, Eq. (53), p. 63 (deterministic, one path): if the
occupation measures `μ_{t_j}` of a measurable path `x` converge weakly to `μ` along `t_j → ∞`, and
`n_j = ⌊t_j / T⌋`, then for every bounded continuous `f : M → ℝ`
`(1/(n_j T)) ∑_{i=0}^{n_j - 1} ∫_{iT}^{(i+1)T} f(x_s) ds → ∫_M f dμ`. -/
theorem block_average_tendsto_eq53
    {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
    (x : ℝ≥0 → M) (hx : Measurable x) (T : ℝ≥0) (hT : 0 < T)
    (t : ℕ → ℝ≥0) (ht : Tendsto t atTop atTop) (μ : ProbabilityMeasure M)
    (hμ : Tendsto (fun j => occupationMeasure x (t j)) atTop (𝓝 μ))
    (f : M → ℝ) (hf : Continuous f) (hfb : ∃ C : ℝ, ∀ y, |f y| ≤ C) :
    Tendsto
      (fun j : ℕ => (1 / ((⌊t j / T⌋₊ : ℝ) * T)) *
        ∑ i ∈ Finset.range ⌊t j / T⌋₊, ∫ s in (i : ℝ) * T..((i : ℝ) + 1) * T, f (x s.toNNReal))
      atTop (𝓝 (∫ y, f y ∂(μ : Measure M))) := by sorry

end StochApproxDyn.WeakAPT

