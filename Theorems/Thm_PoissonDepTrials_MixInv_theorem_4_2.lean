import Mathlib
import Definitions.Def_PoissonDepTrials_MixInv_Setting

open MeasureTheory ProbabilityTheory

namespace PoissonDepTrials.MixInv

theorem theorem_4_2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : ℕ → Ω → ℕ) (hX : IsBernoulliTrials P n X) (φ : ℕ → ℝ) (hφ : IbragimovMixing P X φ) (m : ℕ)
    (h : ℕ → ℝ) (hh : ∀ k, |h k| ≤ 1) :
    |∫ ω, h (W n X ω) ∂P - poissonExp (lam P n X) h| ≤
      2 * (lam P n X)⁻¹ * (8 * m + 5 + 4 * Real.sqrt ((n : ℝ) * φ (m + 1)))
          * (Var[fun ω => (W n X ω : ℝ); P] - lam P n X
              + 2 * (2 * m + 1) * ∑ i ∈ Finset.Icc 1 n, prob P X i ^ 2)
        + 32 * (6 * m + 3 + Real.sqrt ((n : ℝ) * φ (m + 1))) * n * φ (m + 1) := by sorry

end PoissonDepTrials.MixInv

