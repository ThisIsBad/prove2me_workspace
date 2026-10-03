import Mathlib
import Definitions.Def_DiscreteConvex_MConvexSetsB_CharVec
import Definitions.Def_DiscreteConvex_MConvexSetsB_SuppPos
import Definitions.Def_DiscreteConvex_MConvexSetsB_SuppNeg

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.101, axiom (B-EXC[Z]): the M-convex set
exchange axiom, in `DiscreteConvex.MConvexSetsB`.
-/

namespace DiscreteConvex.MConvexSetsB

/-- Axiom **(B-EXC[Z])**: for `x, y ∈ B` and `u ∈ supp⁺(x-y)`, there is `v ∈ supp⁻(x-y)` such
that both `x - χ_u + χ_v` and `y + χ_u - χ_v` lie in `B`. A nonempty set `B ⊆ Zⱽ` satisfying
this is an **M-convex set**. -/
def ExchangeAxiomB {V : Type*} [DecidableEq V] (B : Set (V → ℤ)) : Prop :=
  ∀ x ∈ B, ∀ y ∈ B, ∀ u ∈ SuppPos x y, ∃ v ∈ SuppNeg x y,
    (fun w => x w - CharVec u w + CharVec v w) ∈ B ∧
    (fun w => y w + CharVec u w - CharVec v w) ∈ B

end DiscreteConvex.MConvexSetsB
