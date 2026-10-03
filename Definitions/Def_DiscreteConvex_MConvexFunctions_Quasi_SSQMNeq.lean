import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctions_CharVec
import Definitions.Def_DiscreteConvex_MConvexFunctions_SuppPos
import Definitions.Def_DiscreteConvex_MConvexFunctions_SuppNeg
import Definitions.Def_DiscreteConvex_MConvexFunctions_DomZ

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.172, axiom (SSQM≠): the strict-sense quasi
M-convexity condition relevant to minimization, in `DiscreteConvex.MConvexFunctions.Quasi`.
-/

open DiscreteConvex.MConvexFunctions

namespace DiscreteConvex.MConvexFunctions.Quasi

/-- Axiom **(SSQM≠)** (p.172): for `x, y ∈ dom f` with `f(x) ≠ f(y)` and `u ∈ supp⁺(x-y)`,
there is `v ∈ supp⁻(x-y)` with `f(x-χ_u+χ_v) < f(x)`, or `f(y+χ_u-χ_v) < f(y)`, or both
`f(x-χ_u+χ_v) = f(x)` and `f(y+χ_u-χ_v) = f(y)`. -/
def SSQMNeq {V : Type*} [Fintype V] [DecidableEq V] (f : (V → ℤ) → WithTop ℝ) : Prop :=
  ∀ x ∈ DomZ f, ∀ y ∈ DomZ f, f x ≠ f y → ∀ u ∈ SuppPos x y, ∃ v ∈ SuppNeg x y,
    f (fun w => x w - CharVec u w + CharVec v w) < f x ∨
      f (fun w => y w + CharVec u w - CharVec v w) < f y ∨
      (f (fun w => x w - CharVec u w + CharVec v w) = f x ∧
        f (fun w => y w + CharVec u w - CharVec v w) = f y)

end DiscreteConvex.MConvexFunctions.Quasi
