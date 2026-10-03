import Mathlib
import Definitions.Def_DiscreteConvex_AlgorithmsB_ExchangeAxiomB
import Definitions.Def_DiscreteConvex_AlgorithmsB_VCirc

namespace DiscreteConvex.AlgorithmsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Proposition 10.5 (p.285). If `x∈B` and `u∉V°(x)`, some `x'∈B` has `V°(x')⊇V°(x)∪{u}`. `B` is
bounded, as the page's base polyhedron is: `LBCirc` and `UBCirc` are an infimum and a supremum
over `B`, so on an unbounded `B` they read junk values and `V°(x')` is empty for every `x'`
(`B = {x : x₁ + x₂ = 0, x₁ ≥ 5}` satisfies the exchange axiom and refutes the statement). -/
theorem central_vector_extension (B : Set (V → ℤ)) (hB : ExchangeAxiomB B) (hBbdd : B.Finite)
    (x : V → ℤ)
    (hx : x ∈ B) (u : V) (hu : u ∉ VCirc B x) :
    ∃ x' : V → ℤ, x' ∈ B ∧ VCirc B x ⊆ VCirc B x' ∧ u ∈ VCirc B x' := by sorry

end DiscreteConvex.AlgorithmsB
