import Mathlib

namespace DiscreteConvex.AlgorithmsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `x ∈ B(ρ)`, the base polyhedron. -/
def BasePolyhedronR (rho : Finset V → ℤ) (x : V → ℝ) : Prop :=
  (∀ X : Finset V, ∑ v ∈ X, x v ≤ (rho X : ℝ)) ∧ (∑ v, x v = (rho Finset.univ : ℝ))

end DiscreteConvex.AlgorithmsB
