import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_CharVec
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_SuppPos
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_SuppNeg

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.101, axiom (B-EXC[Z]), in `DiscreteConvex.MConvexFunctionsB`.
-/

namespace DiscreteConvex.MConvexFunctionsB

/-- Axiom **(B-EXC[Z])**: `B ⊆ Zⱽ` is an **M-convex set**. -/
def ExchangeAxiomB {V : Type*} [Fintype V] [DecidableEq V] (B : Set (V → ℤ)) : Prop :=
  ∀ x ∈ B, ∀ y ∈ B, ∀ u ∈ SuppPos x y, ∃ v ∈ SuppNeg x y,
    (fun w => x w - CharVec u w + CharVec v w) ∈ B ∧
    (fun w => y w + CharVec u w - CharVec v w) ∈ B

end DiscreteConvex.MConvexFunctionsB
