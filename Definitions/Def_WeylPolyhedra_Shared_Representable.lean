import Mathlib

namespace WeylPolyhedra.Shared

/-- Weyl (1935), §1, p. 291, (3): a point `x` of `ℝⁿ` is *darstellbar durch `S`* (representable
by the finite point system `S`) when it is a nonnegative linear combination of the points of `S`:
`x = λ a + μ b + ⋯` with `λ ≥ 0, μ ≥ 0, ⋯`. The coefficient function `c` is read only on `S`. -/
def Representable {n : ℕ} (S : Finset (Fin n → ℝ)) (x : Fin n → ℝ) : Prop :=
  ∃ c : (Fin n → ℝ) → ℝ, (∀ s ∈ S, 0 ≤ c s) ∧ x = ∑ s ∈ S, c s • s

end WeylPolyhedra.Shared
