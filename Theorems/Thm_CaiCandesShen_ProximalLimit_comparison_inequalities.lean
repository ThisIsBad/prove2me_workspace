import Mathlib
import Definitions.Def_CaiCandesShen_ProximalLimit_Basic
import Definitions.Def_CaiCandesShen_ProximalLimit_Problems
open Filter Topology

namespace CaiCandesShen.ProximalLimit

/-- Eq. (3.16), p. 1967: for `τ > 0`, with `X⋆_τ` the solution of (3.4) and `X_∞` the minimum
Frobenius norm solution of (1.6),
`‖X⋆_τ‖_* + (1/(2τ))‖X⋆_τ‖_F² ≤ ‖X_∞‖_* + (1/(2τ))‖X_∞‖_F²` and `‖X_∞‖_* ≤ ‖X⋆_τ‖_*`. -/
theorem comparison_inequalities {m n₁ n₂ : ℕ} (f : Fin m → Mat n₁ n₂ → ℝ)
    (Xinf : Mat n₁ n₂) (hXinf : IsMinFrobeniusSolution f Xinf)
    (τ : ℝ) (hτ : 0 < τ) (Xτ : Mat n₁ n₂) (hXτ : IsProximalSolution f τ Xτ) :
    nuclearNorm Xτ + 1 / (2 * τ) * frobNorm Xτ ^ 2 ≤
        nuclearNorm Xinf + 1 / (2 * τ) * frobNorm Xinf ^ 2 ∧
      nuclearNorm Xinf ≤ nuclearNorm Xτ := by sorry

end CaiCandesShen.ProximalLimit
