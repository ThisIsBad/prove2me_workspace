import Mathlib
import Definitions.Def_CaiCandesShen_ProximalLimit_Basic
import Definitions.Def_CaiCandesShen_ProximalLimit_Problems
open Filter Topology

namespace CaiCandesShen.ProximalLimit

/-- Proof of Theorem 3.1, p. 1967: if `τ_k → ∞` and `X⋆_{τ_k} → X_c`, then `X_c = X_∞`. -/
theorem subsequence_limit_eq {m n₁ n₂ : ℕ} (f : Fin m → Mat n₁ n₂ → ℝ)
    (hconv : ∀ i, ConvexOn ℝ Set.univ (f i)) (hlsc : ∀ i, LowerSemicontinuous (f i))
    (Xinf : Mat n₁ n₂) (hXinf : IsMinFrobeniusSolution f Xinf)
    (Xτ : ℝ → Mat n₁ n₂) (hXτ : ∀ τ, 0 < τ → IsProximalSolution f τ (Xτ τ))
    (t : ℕ → ℝ) (ht : Tendsto t atTop atTop) (Xc : Mat n₁ n₂)
    (hXc : Tendsto (fun k => Xτ (t k)) atTop (𝓝 Xc)) :
    Xc = Xinf := by sorry

end CaiCandesShen.ProximalLimit
