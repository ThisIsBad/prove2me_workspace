import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_CharVec
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_SuppPos
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_SuppNeg
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_DomZ

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.135, Eq. (6.11), axiom (M-EXCloc[Z]), in `DiscreteConvex.MConvexFunctionsB`.
-/

namespace DiscreteConvex.MConvexFunctionsB

/-- Axiom **(M-EXCloc[Z])**: (M-EXC[Z]) required only for `x,y` with `‖x-y‖₁ = 4`. -/
def MExchangeAxiomLoc {V : Type*} [Fintype V] [DecidableEq V] (f : (V → ℤ) → WithTop ℝ) : Prop :=
  ∀ x ∈ DomZ f, ∀ y ∈ DomZ f, (∑ v, |x v - y v| = 4) →
    ∃ u ∈ SuppPos x y, ∃ v ∈ SuppNeg x y,
      f x + f y ≥ f (fun w => x w - CharVec u w + CharVec v w) +
        f (fun w => y w + CharVec u w - CharVec v w)

end DiscreteConvex.MConvexFunctionsB
