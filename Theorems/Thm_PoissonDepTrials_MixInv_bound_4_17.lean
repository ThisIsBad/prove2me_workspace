import Mathlib
import Definitions.Def_PoissonDepTrials_MixInv_Setting

open MeasureTheory ProbabilityTheory

namespace PoissonDepTrials.MixInv

theorem bound_4_17 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : ℕ → Ω → ℕ) (hX : IsBernoulliTrials P n X) (φ : ℕ → ℝ) (hφ : IbragimovMixing P X φ) (m : ℕ) (i j : ℕ)
    (hi : i ∈ Finset.Icc 1 n) (hj : j ∈ Finset.Icc 1 n)
    (hij : 0 < |(i : ℤ) - ((j : ℕ) : ℤ)| ∧ |(i : ℤ) - ((j : ℕ) : ℤ)| ≤ m) :
    cov[fun ω => |(Vij n m X i j ω : ℝ) - ∫ ω', (Vij n m X i j ω' : ℝ) ∂P|,
        fun ω => (X i ω : ℝ) * X j ω; P]
      ≤ 4 * n * prob P X i * φ (m + 1) + 4 * lam P n X * φ (m + 1) := by sorry

end PoissonDepTrials.MixInv

