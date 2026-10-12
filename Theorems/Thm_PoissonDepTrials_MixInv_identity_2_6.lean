import Mathlib
import Definitions.Def_PoissonDepTrials_MixInv_Setting

open MeasureTheory ProbabilityTheory

namespace PoissonDepTrials.MixInv

theorem identity_2_6 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : ℕ → Ω → ℕ) (hX : IsBernoulliTrials P n X) (hlam : 0 < lam P n X) (m : ℕ) (h : ℕ → ℝ) (M : ℝ)
    (hM : ∀ k, |h k| ≤ M) :
    ∫ ω, h (W n X ω) ∂P = poissonExp (lam P n X) h
      + (∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n with 0 < |(i : ℤ) - ((j : ℕ) : ℤ)| ∧ |(i : ℤ) - ((j : ℕ) : ℤ)| ≤ m,
          ∫ ω, (X i ω : ℝ) * X j ω *
            delta (stein (lam P n X) h) (Y' n m X i ((j : ℤ) - 1) ω + 1) ∂P)
      + (∑ i ∈ Finset.Icc 1 n,
          ∫ ω, ((X i ω : ℝ) - prob P X i) * stein (lam P n X) h (V n m X i ω + 1) ∂P)
      - ∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n with |(i : ℤ) - ((j : ℕ) : ℤ)| ≤ m,
          prob P X i * ∫ ω, (X j ω : ℝ) *
            delta (stein (lam P n X) h) (Y n m X i ((j : ℤ) - 1) ω + 1) ∂P := by sorry

end PoissonDepTrials.MixInv

