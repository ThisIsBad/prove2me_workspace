import Mathlib
import Definitions.Def_StochApproxDyn_Attractor_Dynamics

open scoped NNReal ENNReal

namespace StochApproxDyn.Attractor

/-- Lemma 6.8 (Benaïm 1999, p. 28). -/
theorem limitSet_subset_of_stepDeviation_lt {M : Type*} [MetricSpace M] [LocallyCompactSpace M]
    (Φ : Flow ℝ≥0 M) (A : Set M) (hA : StochApproxDyn.LimitSet.IsAttractor Φ A) (K : Set M) (hKne : K.Nonempty)
    (hK : IsCompact K) (hKB : K ⊆ StochApproxDyn.LimitSet.basin Φ A) :
    ∃ T : ℝ≥0, 0 < T ∧ ∃ δ : ℝ≥0, 0 < δ ∧
      ∀ X : ℝ≥0 → M, StochApproxDyn.LimitSet.IsAsymptoticPseudotrajectory Φ X → X 0 ∈ K →
        stepDeviation Φ X T < (δ : ℝ≥0∞) → StochApproxDyn.LimitSet.limitSet X ⊆ A := by sorry

end StochApproxDyn.Attractor

