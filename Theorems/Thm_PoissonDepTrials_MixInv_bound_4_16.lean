import Mathlib
import Definitions.Def_PoissonDepTrials_MixInv_Setting

open MeasureTheory ProbabilityTheory

namespace PoissonDepTrials.MixInv

theorem bound_4_16 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : ℕ → Ω → ℕ) (hX : IsBernoulliTrials P n X) (φ : ℕ → ℝ) (hφ : IbragimovMixing P X φ) (m : ℕ) (i j : ℕ) :
    ∫ ω, |(Vij n m X i j ω : ℝ) - ∫ ω', (Vij n m X i j ω' : ℝ) ∂P| ∂P
        ≤ Real.sqrt (Var[fun ω => (Vij n m X i j ω : ℝ); P]) ∧
      Real.sqrt (Var[fun ω => (Vij n m X i j ω : ℝ); P])
        ≤ Real.sqrt (lam P n X) * (m + 1 + 2 * Real.sqrt ((n : ℝ) * φ (m + 1))) := by sorry

end PoissonDepTrials.MixInv

