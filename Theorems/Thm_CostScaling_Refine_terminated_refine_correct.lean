import Mathlib
import Definitions.Def_CostScaling_Refine_Run

namespace CostScaling.Refine

/-- Theorem 5.4, p. 21, including the entry contract of refine. -/
theorem terminated_refine_correct {V : Type*} [Fintype V] [DecidableEq V]
    (N : Network V) (ε : ℝ) (hε : 0 < ε)
    (f₀ : V → V → ℝ) (p₀ : V → ℝ)
    (hcirc : CycleCanceling.MinMean.IsCirculation N f₀)
    (hentry : IsEpsOptimal N (2 * ε) f₀ p₀)
    (σ : ℕ → State V) (K : ℕ)
    (hrun : IsRun N ε f₀ p₀ σ K)
    (hterm : Terminated N (σ K)) :
    CycleCanceling.MinMean.IsCirculation N (σ K).f ∧
      IsEpsOptimal N ε (σ K).f (σ K).p := by sorry

end CostScaling.Refine

