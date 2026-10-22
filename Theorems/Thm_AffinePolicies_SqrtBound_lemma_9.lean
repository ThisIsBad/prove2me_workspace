import Mathlib
import Definitions.Def_AffinePolicies_SqrtBound_Setting

open Matrix

namespace AffinePolicies.SqrtBound

theorem lemma_9 {m : ℕ} (U : Set (Fin m → ℝ)) (hUnn : ∀ b ∈ U, 0 ≤ b)
    (μ : Fin m → ℝ) (hμ : ∀ j, IsGreatest ((fun b : Fin m → ℝ => b j) '' U) (μ j))
    (K : ℕ) (u : ℕ → Fin m → ℝ) (hrun : IsRun U μ K u) :
    (∀ b ∈ U, scaledSum μ (J1 μ u K) b ≤ Real.sqrt m) ∧
      ∀ j, j ∉ J1 μ u K → ∀ b ∈ U, b j ≤ betaSum u K j := by sorry

end AffinePolicies.SqrtBound

