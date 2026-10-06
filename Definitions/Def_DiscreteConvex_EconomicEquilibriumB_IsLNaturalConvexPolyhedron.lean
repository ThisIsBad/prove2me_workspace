import Mathlib

namespace DiscreteConvex.EconomicEquilibriumB

open Classical
open scoped Pointwise
variable {K : Type*} [Fintype K] [DecidableEq K]
/-- `P ⊆ Rᴷ` is an L♮-convex polyhedron (axiom (SBS♮[R]), Eq. (5.20)). -/
def IsLNaturalConvexPolyhedron (P : Set (K → ℝ)) : Prop :=
  ∀ p ∈ P, ∀ q ∈ P, ∀ alpha : ℝ, 0 ≤ alpha →
    (fun k => max (p k - alpha) (q k)) ∈ P ∧ (fun k => min (p k) (q k + alpha)) ∈ P

end DiscreteConvex.EconomicEquilibriumB
