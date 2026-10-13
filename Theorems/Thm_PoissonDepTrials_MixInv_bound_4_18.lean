import Mathlib
import Definitions.Def_PoissonDepTrials_MixInv_Setting

open MeasureTheory ProbabilityTheory

namespace PoissonDepTrials.MixInv

theorem bound_4_18 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : ℕ → Ω → ℕ) (hX : IsBernoulliTrials P n X) (φ : ℕ → ℝ) (hφ : IbragimovMixing P X φ) (m : ℕ) (i j : ℕ)
    (hi : i ∈ Finset.Icc 1 n) (hj : j ∈ Finset.Icc 1 n)
    (hij : 0 < |(i : ℤ) - ((j : ℕ) : ℤ)| ∧ |(i : ℤ) - ((j : ℕ) : ℤ)| ≤ m) :
    ∫ ω, (X i ω : ℝ) * X j ω *
        (1 + 2 * min (1 / Real.sqrt (lam P n X)) 1 * |(Y' n m X i ((j : ℤ) - 1) ω : ℝ) + 1 - lam P n X|) ∂P
      ≤ (∫ ω, (X i ω : ℝ) * X j ω ∂P) * (8 * m + 5 + 4 * Real.sqrt ((n : ℝ) * φ (m + 1)))
        + 8 * min (1 / Real.sqrt (lam P n X)) 1 * (n * prob P X i + lam P n X) * φ (m + 1) := by sorry

end PoissonDepTrials.MixInv

