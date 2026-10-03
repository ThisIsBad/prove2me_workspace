import Mathlib

open Filter

namespace LeblSCV.Holomorphic

/-- Definition 1.1.2 (Lebl, p. 14). A function `f` on an open set `U ⊆ ℂⁿ` is holomorphic if it is
locally bounded (every `p ∈ U` has a neighborhood `N` on which `f` is bounded) and
complex-differentiable in each variable separately: for every `z ∈ U` and every `k`, the limit
`lim_{ξ → 0} (f(z_1, …, z_k + ξ, …, z_n) - f(z)) / ξ` exists, i.e. the one-variable function
`ξ ↦ f(z_1, …, z_k + ξ, …, z_n)` is complex-differentiable at `ξ = 0`.
Only the values of `f` on `U` matter when `U` is open. -/
def IsHolomorphicOn {n : ℕ} (f : (Fin n → ℂ) → ℂ) (U : Set (Fin n → ℂ)) : Prop :=
  (∀ p ∈ U, ∃ N ∈ nhds p, ∃ M : ℝ, ∀ w ∈ N ∩ U, ‖f w‖ ≤ M) ∧
  (∀ z ∈ U, ∀ k : Fin n,
    DifferentiableAt ℂ (fun ξ : ℂ => f (Function.update z k (z k + ξ))) 0)

end LeblSCV.Holomorphic
