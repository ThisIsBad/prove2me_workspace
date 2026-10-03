import Mathlib
import Definitions.Def_DiscreteConvex_AlgorithmsB_SuppPos
import Definitions.Def_DiscreteConvex_AlgorithmsB_SuppNeg

namespace DiscreteConvex.AlgorithmsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Axiom (B-EXC[Z]): `B` is an M-convex set. -/
def ExchangeAxiomB (B : Set (V → ℤ)) : Prop :=
  ∀ x ∈ B, ∀ y ∈ B, ∀ u ∈ SuppPos x y, ∃ v ∈ SuppNeg x y,
    (fun w => x w - (if w = u then (1:ℤ) else 0) + (if w = v then (1:ℤ) else 0)) ∈ B ∧
    (fun w => y w + (if w = u then (1:ℤ) else 0) - (if w = v then (1:ℤ) else 0)) ∈ B

end DiscreteConvex.AlgorithmsB
