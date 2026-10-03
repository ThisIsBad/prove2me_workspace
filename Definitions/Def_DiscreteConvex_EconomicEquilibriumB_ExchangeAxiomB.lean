import Mathlib

namespace DiscreteConvex.EconomicEquilibriumB

open Classical
open scoped Pointwise
variable {K : Type*} [Fintype K] [DecidableEq K]
/-- Axiom (B-EXC[Z]): `B` is an M-convex set. -/
def ExchangeAxiomB (B : Set (Option K → ℤ)) : Prop :=
  ∀ x ∈ B, ∀ y ∈ B, ∀ u ∈ Finset.univ.filter (fun v => y v < x v),
    ∃ v ∈ Finset.univ.filter (fun v => x v < y v),
      (fun w => x w - (if w = u then (1:ℤ) else 0) + (if w = v then (1:ℤ) else 0)) ∈ B ∧
      (fun w => y w + (if w = u then (1:ℤ) else 0) - (if w = v then (1:ℤ) else 0)) ∈ B

end DiscreteConvex.EconomicEquilibriumB
