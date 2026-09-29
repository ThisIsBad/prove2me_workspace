import Mathlib
import Definitions.Def_CaiCandesShen_Convergence_Iterations
open Filter Topology

namespace CaiCandesShen.Convergence

/-- Theorem 4.2, second sentence, p. 1968: if `0 < inf δ_k ≤ sup δ_k < 2`, the sequence `X^k`
produced by the SVT iteration (2.7) from `Y⁰ = 0` converges to the unique solution of (2.8). -/
theorem svt_converges {n₁ n₂ : ℕ} (τ : ℝ) (hτ : 0 < τ) (Ω : Finset (Fin n₁ × Fin n₂))
    (M : Mat n₁ n₂) (δ : ℕ → ℝ)
    (hδ : ∃ a C : ℝ, 0 < a ∧ C < 2 ∧ ∀ k : ℕ, 1 ≤ k → a ≤ δ k ∧ δ k ≤ C)
    (X Y : ℕ → Mat n₁ n₂) (hXY : IsSVTSeq τ Ω M δ X Y) :
    (∃! Xs : Mat n₁ n₂, IsSol28 τ Ω M Xs) ∧
      ∀ Xs : Mat n₁ n₂, IsSol28 τ Ω M Xs → Tendsto X atTop (𝓝 Xs) := by sorry

end CaiCandesShen.Convergence
