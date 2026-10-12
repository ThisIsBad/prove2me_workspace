import Mathlib
import Definitions.Def_PoissonDepTrials_MixSqrt_Setting

open MeasureTheory ProbabilityTheory

namespace PoissonDepTrials.MixSqrt

/-- Chen (1975), Lemma 4.5, p. 540, (4.9): for Bernoulli trials satisfying (4.1),
`ΣΣ_{0<|i−j|≤m} EX_iX_j ≤ Var(W) − λ + (2m + 1) Σ_i p_i² + 4λnφ(m + 1)`. -/
theorem lemma_4_5 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : ℕ → Ω → ℕ) (hX : IsBernoulliTrials P n X) (φ : ℕ → ℝ)
    (hφ : IbragimovMixing P X φ) (m : ℕ) :
    ∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n with 0 < |(i : ℤ) - (j : ℕ)| ∧ |(i : ℤ) - (j : ℕ)| ≤ m,
        ∫ ω, (X i ω : ℝ) * X j ω ∂P
      ≤ Var[fun ω => (W n X ω : ℝ); P] - lam P n X + (2 * m + 1) * ∑ i ∈ Finset.Icc 1 n, prob P X i ^ 2
        + 4 * lam P n X * n * φ (m + 1) := by sorry

end PoissonDepTrials.MixSqrt

