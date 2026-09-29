import Mathlib

namespace WeylPolyhedra.Shared

/-- Weyl (1935), §1, p. 291, (2): the finite point system `S ⊆ ℝⁿ` is *nicht-ausgeartet*
(non-degenerate) when its points do not all satisfy one linear equation
`a₁x₁ + ⋯ + aₙxₙ = 0` with `(a₁, ⋯, aₙ) ≠ (0, ⋯, 0)`: the only `α` with `α ⬝ᵥ s = 0` for every
`s ∈ S` is `α = 0`. -/
def NonDegenerate {n : ℕ} (S : Finset (Fin n → ℝ)) : Prop :=
  ∀ α : Fin n → ℝ, (∀ s ∈ S, α ⬝ᵥ s = 0) → α = 0

end WeylPolyhedra.Shared
