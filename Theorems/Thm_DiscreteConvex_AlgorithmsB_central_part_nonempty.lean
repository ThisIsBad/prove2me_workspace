import Mathlib
import Definitions.Def_DiscreteConvex_AlgorithmsB_ExchangeAxiomB
import Definitions.Def_DiscreteConvex_AlgorithmsB_BCirc

namespace DiscreteConvex.AlgorithmsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Proposition 10.6 (p.285). `B° ≠ ∅` if `B` is a bounded nonempty M-convex set. -/
theorem central_part_nonempty (B : Set (V → ℤ)) (hB : ExchangeAxiomB B) (hBne : B.Nonempty)
    (hBbdd : ∃ N : ℤ, ∀ y ∈ B, ∀ v, -N ≤ y v ∧ y v ≤ N) :
    (BCirc B).Nonempty := by sorry

end DiscreteConvex.AlgorithmsB
