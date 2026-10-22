import Mathlib
import Definitions.Def_AffinePolicies_SqrtBound_Setting

open Matrix

namespace AffinePolicies.SqrtBound

theorem lemma_10 {m : ℕ} (U : Set (Fin m → ℝ))
    (μ : Fin m → ℝ) (hμ : ∀ j, IsGreatest ((fun b : Fin m → ℝ => b j) '' U) (μ j))
    (hμpos : ∀ j, 0 < μ j)
    (K : ℕ) (u : ℕ → Fin m → ℝ) (hiter : ∀ k < K, IsIteration U μ u k) :
    (K : ℝ) ≤ 2 * Real.sqrt m := by sorry

end AffinePolicies.SqrtBound

