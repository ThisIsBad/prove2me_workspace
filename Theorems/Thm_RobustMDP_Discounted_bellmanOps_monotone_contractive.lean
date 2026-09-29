import Mathlib
import Definitions.Def_RobustMDP_Discounted_Model
import Definitions.Def_RobustMDP_Shared_supportFunction
import Definitions.Def_RobustMDP_Discounted_bellmanOps

namespace RobustMDP.Discounted

/-- Nilim–El Ghaoui 2005, p. 786: the maps `g` of (29) (the robust Bellman operator) and of (30)
(robust evaluation of a stationary policy `π`) are componentwise nondecreasing and `ν`-contractive
in the sup norm `‖·‖_∞` (the sup metric of `Fin n → ℝ`): for all `u, v ∈ ℝⁿ`,
`‖g(u) − g(v)‖_∞ ≤ ν ‖u − v‖_∞`. Only `𝒫_i^a ⊆ Δ_n` and nonemptiness of the row sets are
assumed. -/
theorem bellmanOps_monotone_contractive {n : ℕ} {A : Type} [Fintype A] [Nonempty A]
    (M : Model n A) :
    (Monotone M.bellmanOp ∧ LipschitzWith ⟨M.discount, M.discount_nonneg⟩ M.bellmanOp) ∧
    ∀ π : StationaryPolicy n A,
      Monotone (M.policyOp π) ∧ LipschitzWith ⟨M.discount, M.discount_nonneg⟩ (M.policyOp π) := by sorry

end RobustMDP.Discounted
