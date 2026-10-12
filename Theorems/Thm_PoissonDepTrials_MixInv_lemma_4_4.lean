import Mathlib
import Definitions.Def_PoissonDepTrials_MixInv_Setting

open MeasureTheory ProbabilityTheory

namespace PoissonDepTrials.MixInv

theorem lemma_4_4 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : ℕ → Ω → ℕ) (hX : IsBernoulliTrials P n X) (φ : ℕ → ℝ) (hφ : IbragimovMixing P X φ) (m : ℕ) :
    Real.sqrt (Var[fun ω => (W n X ω : ℝ); P]) ≤
      Real.sqrt (lam P n X) * (m + 1 + 2 * Real.sqrt ((n : ℝ) * φ (m + 1))) := by sorry

end PoissonDepTrials.MixInv

