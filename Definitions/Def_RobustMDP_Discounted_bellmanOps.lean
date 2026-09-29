import Mathlib
import Definitions.Def_RobustMDP_Discounted_Model
import Definitions.Def_RobustMDP_Shared_supportFunction

namespace RobustMDP.Discounted

/-- The robust Bellman operator `g` of (29) (p. 786), the right side of (19)/(20):
`(g(v))_i = min_{a ∈ 𝒜} (c(i, a) + ν σ_{𝒫_i^a}(v))`, a minimum over the finite nonempty
action set. -/
noncomputable def Model.bellmanOp {n : ℕ} {A : Type} [Fintype A] [Nonempty A] (M : Model n A)
    (v : Fin n → ℝ) : Fin n → ℝ :=
  fun i => Finset.univ.inf' Finset.univ_nonempty
    (fun a => M.cost i a + M.discount * Shared.supportFunction (M.rows a i) v)

/-- The robust policy-evaluation operator of (30) (p. 786), the right side of (23), for a
stationary policy `π = (𝐚, 𝐚, …)`: `(g(v))_i = c(i, 𝐚(i)) + ν σ_{𝒫_i^{𝐚(i)}}(v)`. -/
noncomputable def Model.policyOp {n : ℕ} {A : Type} (M : Model n A) (π : StationaryPolicy n A)
    (v : Fin n → ℝ) : Fin n → ℝ :=
  fun i => M.cost i (π i) + M.discount * Shared.supportFunction (M.rows (π i) i) v

end RobustMDP.Discounted
