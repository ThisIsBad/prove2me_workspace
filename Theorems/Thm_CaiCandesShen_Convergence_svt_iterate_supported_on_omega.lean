import Mathlib
import Definitions.Def_CaiCandesShen_Convergence_Iterations

namespace CaiCandesShen.Convergence

/-- §2.2, p. 1961 (Sparsity): since `Y⁰ = 0`, every iterate `Y^k` of (2.7) vanishes outside `Ω`,
i.e. `Y^k = P_Ω(Y^k)` for all `k ≥ 0`. -/
theorem svt_iterate_supported_on_omega {n₁ n₂ : ℕ} (τ : ℝ) (hτ : 0 < τ)
    (Ω : Finset (Fin n₁ × Fin n₂)) (M : Mat n₁ n₂) (δ : ℕ → ℝ) (hδ : ∀ k, 1 ≤ k → 0 < δ k)
    (X Y : ℕ → Mat n₁ n₂) (hXY : IsSVTSeq τ Ω M δ X Y) :
    ∀ k : ℕ, projΩ Ω (Y k) = Y k := by sorry

end CaiCandesShen.Convergence
