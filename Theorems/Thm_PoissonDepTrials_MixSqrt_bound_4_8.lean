import Mathlib
import Definitions.Def_PoissonDepTrials_MixSqrt_Setting

open MeasureTheory ProbabilityTheory

namespace PoissonDepTrials.MixSqrt

/-- Chen (1975), proof of Lemma 4.4, p. 540, (4.8): for Bernoulli trials satisfying (4.1),
`|Σ_{i=1}^n E[(X_i − p_i)V^{(i)}]| ≤ 4λnφ(m + 1)`. -/
theorem bound_4_8 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : ℕ → Ω → ℕ) (hX : IsBernoulliTrials P n X) (φ : ℕ → ℝ)
    (hφ : IbragimovMixing P X φ) (m : ℕ) :
    |∑ i ∈ Finset.Icc 1 n, ∫ ω, ((X i ω : ℝ) - prob P X i) * (V n m X i ω : ℝ) ∂P|
      ≤ 4 * lam P n X * n * φ (m + 1) := by sorry

end PoissonDepTrials.MixSqrt

