import Mathlib
import Definitions.Def_CaiCandesShen_ProximalLimit_Basic
import Definitions.Def_CaiCandesShen_ProximalLimit_Problems
open Filter Topology

namespace CaiCandesShen.ProximalLimit

/-- Proof of Theorem 3.1, p. 1967 (display after (3.17)): `lim_{τ→∞} ‖X⋆_τ‖_* = ‖X_∞‖_*`. -/
theorem nuclearNorm_tendsto {m n₁ n₂ : ℕ} (f : Fin m → Mat n₁ n₂ → ℝ)
    (Xinf : Mat n₁ n₂) (hXinf : IsMinFrobeniusSolution f Xinf)
    (Xτ : ℝ → Mat n₁ n₂) (hXτ : ∀ τ, 0 < τ → IsProximalSolution f τ (Xτ τ)) :
    Tendsto (fun τ => nuclearNorm (Xτ τ)) atTop (𝓝 (nuclearNorm Xinf)) := by sorry

end CaiCandesShen.ProximalLimit
