import Mathlib
import Definitions.Def_PoissonDepTrials_MixInv_Setting

open MeasureTheory ProbabilityTheory

namespace PoissonDepTrials.MixInv

theorem bound_4_14 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : ℕ → Ω → ℕ) (hX : IsBernoulliTrials P n X) (hlam : 0 < lam P n X) (φ : ℕ → ℝ) (hφ : IbragimovMixing P X φ) (m : ℕ)
    (h : ℕ → ℝ) (hh : ∀ k, |h k| ≤ 1) :
    |∫ ω, h (W n X ω) ∂P - poissonExp (lam P n X) h| ≤
      2 * (lam P n X)⁻¹ * (∑ i ∈ Finset.Icc 1 n,
          ∑ j ∈ Finset.Icc 1 n with 0 < |(i : ℤ) - ((j : ℕ) : ℤ)| ∧ |(i : ℤ) - ((j : ℕ) : ℤ)| ≤ m,
            ∫ ω, (X i ω : ℝ) * X j ω *
              (1 + 2 * min (1 / Real.sqrt (lam P n X)) 1 * |(Y' n m X i ((j : ℤ) - 1) ω : ℝ) + 1 - lam P n X|) ∂P)
      + 2 * (lam P n X)⁻¹ * (∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n with |(i : ℤ) - ((j : ℕ) : ℤ)| ≤ m,
            prob P X i * ∫ ω, (X j ω : ℝ) *
              (1 + 2 * min (1 / Real.sqrt (lam P n X)) 1 * |(Y n m X i ((j : ℤ) - 1) ω : ℝ) + 1 - lam P n X|) ∂P)
      + 24 * min (1 / Real.sqrt (lam P n X)) 1 * n * φ (m + 1) := by sorry

end PoissonDepTrials.MixInv

