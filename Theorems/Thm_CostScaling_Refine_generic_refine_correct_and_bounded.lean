import Mathlib
import Definitions.Def_CostScaling_Refine_Run

namespace CostScaling.Refine

/-- Theorem 5.4 and Lemmas 5.1, 5.9–5.11, with the paper's constants. -/
theorem generic_refine_correct_and_bounded {V : Type*} [Fintype V] [DecidableEq V]
    (N : Network V) (ε : ℝ) (hε : 0 < ε)
    (f₀ : V → V → ℝ) (p₀ : V → ℝ)
    (hcirc : CycleCanceling.MinMean.IsCirculation N f₀)
    (hentry : IsEpsOptimal N (2 * ε) f₀ p₀)
    (σ : ℕ → State V) (K : ℕ)
    (hrun : IsRun N ε f₀ p₀ σ K) :
    K ≤ 3 * Fintype.card V * (Fintype.card V - 1) +
        3 * Fintype.card V * N.E.card +
        3 * Fintype.card V ^ 2 * (N.E.card + Fintype.card V) ∧
    (∀ v, IsActive N (σ K).f v → ∃ t, IsStep N ε (σ K) t) ∧
    (Terminated N (σ K) →
      CycleCanceling.MinMean.IsCirculation N (σ K).f ∧
      IsEpsOptimal N ε (σ K).f (σ K).p) := by sorry

end CostScaling.Refine

