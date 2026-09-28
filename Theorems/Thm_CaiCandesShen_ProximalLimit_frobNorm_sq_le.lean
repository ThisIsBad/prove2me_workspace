import Mathlib
import Definitions.Def_CaiCandesShen_ProximalLimit_Basic
import Definitions.Def_CaiCandesShen_ProximalLimit_Problems
open Filter Topology

namespace CaiCandesShen.ProximalLimit

/-- Eq. (3.17), p. 1967: for every `τ > 0`, `‖X⋆_τ‖_F² ≤ ‖X_∞‖_F²`, so `‖X⋆_τ‖_F²` is bounded
uniformly in `τ`. -/
theorem frobNorm_sq_le {m n₁ n₂ : ℕ} (f : Fin m → Mat n₁ n₂ → ℝ)
    (Xinf : Mat n₁ n₂) (hXinf : IsMinFrobeniusSolution f Xinf)
    (Xτ : ℝ → Mat n₁ n₂) (hXτ : ∀ τ, 0 < τ → IsProximalSolution f τ (Xτ τ)) :
    ∀ τ, 0 < τ → frobNorm (Xτ τ) ^ 2 ≤ frobNorm Xinf ^ 2 := by sorry

end CaiCandesShen.ProximalLimit
