import Mathlib
import Definitions.Def_CaiCandesShen_ProximalLimit_Basic
import Definitions.Def_CaiCandesShen_ProximalLimit_Problems
open Filter Topology

namespace CaiCandesShen.ProximalLimit

/-- Theorem 3.1, p. 1967: let `X⋆_τ` be the solution to (3.4) and `X_∞` the minimum Frobenius norm
solution (3.14) to (1.6). If the `f_i` are convex and lower semicontinuous, then
`lim_{τ→∞} ‖X⋆_τ - X_∞‖_F = 0` (eq. (3.15)). -/
theorem proximal_solution_tendsto_min_norm {m n₁ n₂ : ℕ} (f : Fin m → Mat n₁ n₂ → ℝ)
    (hconv : ∀ i, ConvexOn ℝ Set.univ (f i)) (hlsc : ∀ i, LowerSemicontinuous (f i))
    (Xinf : Mat n₁ n₂) (hXinf : IsMinFrobeniusSolution f Xinf)
    (Xτ : ℝ → Mat n₁ n₂) (hXτ : ∀ τ, 0 < τ → IsProximalSolution f τ (Xτ τ)) :
    Tendsto (fun τ => frobNorm (Xτ τ - Xinf)) atTop (𝓝 0) := by sorry

end CaiCandesShen.ProximalLimit

