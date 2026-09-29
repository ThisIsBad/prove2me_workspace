import Mathlib
import Definitions.Def_CaiCandesShen_Convergence_Iterations
open Filter Topology

namespace CaiCandesShen.Convergence

/-- Theorem 4.2, first sentence, p. 1968: if `0 < inf δ_k ≤ sup δ_k < 2/‖𝒜‖²`, the sequence `X^k`
produced by Uzawa's iteration (3.3) from `y⁰ = 0` converges to the unique solution of (3.1).
The step-size condition is written multiplicatively (`C‖𝒜‖² < 2`); feasibility of (3.1) is
assumed, as "the unique solution" presupposes it. -/
theorem uzawa_converges {n₁ n₂ m : ℕ} (τ : ℝ) (hτ : 0 < τ) (Aop : Fin m → Mat n₁ n₂)
    (b : Fin m → ℝ) (hfeas : ∃ X : Mat n₁ n₂, applyA Aop X = b) (δ : ℕ → ℝ)
    (hδ : ∃ a C : ℝ, 0 < a ∧ C * opNormA Aop ^ 2 < 2 ∧ ∀ k : ℕ, 1 ≤ k → a ≤ δ k ∧ δ k ≤ C)
    (X : ℕ → Mat n₁ n₂) (y : ℕ → Fin m → ℝ) (hXy : IsUzawaSeq τ Aop b δ X y) :
    (∃! Xs : Mat n₁ n₂, IsSol31 τ Aop b Xs) ∧
      ∀ Xs : Mat n₁ n₂, IsSol31 τ Aop b Xs → Tendsto X atTop (𝓝 Xs) := by sorry

end CaiCandesShen.Convergence
