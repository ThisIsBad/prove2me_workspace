import Mathlib
import Definitions.Def_ClarkeGradients_Shared_LipschitzOnBounded
import Definitions.Def_ClarkeGradients_Shared_generalizedGradient

open Filter Topology

namespace ClarkeGradients.MaxFunctions

/-- Clarke (1975), Corollary (1.10): for locally Lipschitz `f`, if
`ζ · v ≤ limsup_{δ ↓ 0} [f(x + δv) - f(x)] / δ` for all `v ∈ ℝⁿ`, then `ζ ∈ ∂f(x)`. -/
theorem mem_generalizedGradient_of_le_limsup {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : Shared.LipschitzOnBounded f) (x ζ : EuclideanSpace ℝ (Fin n))
    (h : ∀ v : EuclideanSpace ℝ (Fin n),
      inner ℝ ζ v ≤ limsup (fun δ : ℝ => (f (x + δ • v) - f x) / δ) (𝓝[>] (0 : ℝ))) :
    ζ ∈ Shared.generalizedGradient f x := by sorry

end ClarkeGradients.MaxFunctions
