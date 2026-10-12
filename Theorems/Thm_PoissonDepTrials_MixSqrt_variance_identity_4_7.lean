import Mathlib
import Definitions.Def_PoissonDepTrials_MixSqrt_Setting

open MeasureTheory ProbabilityTheory

namespace PoissonDepTrials.MixSqrt

/-- Chen (1975), proof of Lemma 4.4, p. 540, (4.7): for an arbitrary sequence of dependent
Bernoulli trials,
`Var(W) = λ + ΣΣ_{0<|i−j|≤m} EX_iX_j − ΣΣ_{|i−j|≤m} p_ip_j + Σ_i E[(X_i − p_i)V^{(i)}]`. -/
theorem variance_identity_4_7 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : ℕ → Ω → ℕ) (hX : IsBernoulliTrials P n X) (m : ℕ) :
    Var[fun ω => (W n X ω : ℝ); P] = lam P n X
      + (∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n with 0 < |(i : ℤ) - (j : ℕ)| ∧ |(i : ℤ) - (j : ℕ)| ≤ m,
          ∫ ω, (X i ω : ℝ) * X j ω ∂P)
      - (∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n with |(i : ℤ) - (j : ℕ)| ≤ m,
          prob P X i * prob P X j)
      + ∑ i ∈ Finset.Icc 1 n, ∫ ω, ((X i ω : ℝ) - prob P X i) * (V n m X i ω : ℝ) ∂P := by sorry

end PoissonDepTrials.MixSqrt

