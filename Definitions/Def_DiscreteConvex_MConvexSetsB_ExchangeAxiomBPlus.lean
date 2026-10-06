import Mathlib
import Definitions.Def_DiscreteConvex_MConvexSetsB_CharVec
import Definitions.Def_DiscreteConvex_MConvexSetsB_SuppPos
import Definitions.Def_DiscreteConvex_MConvexSetsB_SuppNeg

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.102, axiom (B-EXC+[Z]): the "one-sided
plus" variant of the M-convex set exchange axiom, in `DiscreteConvex.MConvexSetsB`.
-/

namespace DiscreteConvex.MConvexSetsB

/-- Axiom **(B-EXC+[Z])**: for `x, y ∈ B` and `u ∈ supp⁺(x-y)`, there is `v ∈ supp⁻(x-y)` such
that `y + χ_u - χ_v ∈ B` (only the `y`-side of (B-EXC[Z]) is required). -/
def ExchangeAxiomBPlus {V : Type*} [DecidableEq V] (B : Set (V → ℤ)) : Prop :=
  ∀ x ∈ B, ∀ y ∈ B, ∀ u ∈ SuppPos x y, ∃ v ∈ SuppNeg x y,
    (fun w => y w + CharVec u w - CharVec v w) ∈ B

end DiscreteConvex.MConvexSetsB
