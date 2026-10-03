import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_CharVec
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_SuppPos
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_SuppNeg
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_DomZ

namespace DiscreteConvex.MConvexFunctionsE

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Axiom (M-EXCw[Z]), the weak exchange axiom (Theorem 6.5): `∃u, ∃v` in place of `∀u, ∃v`. -/
def MExchangeAxiomW (f : (V → ℤ) → WithTop ℝ) : Prop :=
  ∃ x ∈ DomZ f, ∃ y ∈ DomZ f, x ≠ y ∧ ∃ u ∈ SuppPos x y, ∃ v ∈ SuppNeg x y,
    f x + f y ≥ f (fun w => x w - CharVec u w + CharVec v w) +
      f (fun w => y w + CharVec u w - CharVec v w)

end DiscreteConvex.MConvexFunctionsE
