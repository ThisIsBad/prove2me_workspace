import Mathlib

namespace RelaxationMethod.ConvexDomain

/-- §9, p. 402: the closed half-space `H` belongs to the family `F` of `A`: `H = {x | c ≤ ⟪u, x⟫}`
for some nonzero `u` and real `c`, `A ⊆ H`, and the bounding hyperplane `{x | ⟪u, x⟫ = c}` meets
`A` (it is a hyperplane of support of `A`). -/
def IsSupportHalfSpace {n : ℕ} (A : Set (EuclideanSpace ℝ (Fin n)))
    (H : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∃ u : EuclideanSpace ℝ (Fin n), u ≠ 0 ∧ ∃ c : ℝ,
    H = {x | c ≤ inner ℝ u x} ∧ A ⊆ H ∧ ∃ a ∈ A, inner ℝ u a = c

end RelaxationMethod.ConvexDomain
