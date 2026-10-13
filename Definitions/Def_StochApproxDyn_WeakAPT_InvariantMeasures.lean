import Mathlib

namespace StochApproxDyn.WeakAPT

open MeasureTheory
open scoped NNReal

/-- The set `𝓜(Φ) ⊂ 𝓟(M)` of `Φ`-invariant Borel probability measures of a semiflow
`Φ : ℝ≥0 × M → M` (Benaïm 1999, §8.3, p. 43, and §10, p. 61). For a semiflow, invariance is
taken in the push-forward sense `(Φ_t)_* μ = μ` for every `t ≥ 0`, i.e. `μ(Φ_t⁻¹(A)) = μ(A)` for
every Borel set `A` and every `t ≥ 0`; this is the form used in the proof of Theorem 10.1
(`∫ f ∘ Φ_T dμ = ∫ f dμ`, p. 63). For a flow it coincides with the definition
`μ(A) = μ(Φ_t(A))` for all `t ∈ ℝ` of §8.3. `ProbabilityMeasure M` carries Mathlib's topology of
weak convergence (convergence against bounded continuous functions). -/
def invariantMeasures {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
    (Φ : Flow ℝ≥0 M) : Set (ProbabilityMeasure M) :=
  {μ | ∀ t : ℝ≥0, (μ : Measure M).map (Φ t) = (μ : Measure M)}

end StochApproxDyn.WeakAPT
