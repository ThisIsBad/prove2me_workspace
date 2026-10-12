import Mathlib
import Definitions.Def_PoissonDepTrials_MixSqrt_Setting

open MeasureTheory ProbabilityTheory

namespace PoissonDepTrials.MixSqrt

/-- Chen (1975), Lemma 4.6, p. 540, (4.11). For Bernoulli trials satisfying (4.1) and every
function `f` on the nonnegative integers bounded by `M`,
`|Σ_{i=1}^n E[(X_i − p_i)f(V^{(i)} + 1)]| ≤ 6‖f‖nφ(m + 1)`. -/
theorem lemma_4_6 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : ℕ → Ω → ℕ) (hX : IsBernoulliTrials P n X) (φ : ℕ → ℝ)
    (hφ : IbragimovMixing P X φ) (m : ℕ) (f : ℕ → ℝ) (M : ℝ) (hM : ∀ k, |f k| ≤ M) :
    |∑ i ∈ Finset.Icc 1 n, ∫ ω, ((X i ω : ℝ) - prob P X i) * f (V n m X i ω + 1) ∂P|
      ≤ 6 * M * n * φ (m + 1) := by sorry

end PoissonDepTrials.MixSqrt

