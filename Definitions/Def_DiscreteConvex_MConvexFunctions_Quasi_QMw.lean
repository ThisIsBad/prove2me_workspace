import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctions_CharVec
import Definitions.Def_DiscreteConvex_MConvexFunctions_SuppPos
import Definitions.Def_DiscreteConvex_MConvexFunctions_SuppNeg
import Definitions.Def_DiscreteConvex_MConvexFunctions_DomZ

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.169, axiom (QMw): the weak quasi M-convexity
condition, in `DiscreteConvex.MConvexFunctions.Quasi`. Builds on chunk `06-mconvex-functions-i`'s
`DiscreteConvex.MConvexFunctions` definitions per the series' shared book namespace.
-/

open DiscreteConvex.MConvexFunctions

namespace DiscreteConvex.MConvexFunctions.Quasi

/-- Axiom **(QMw)** (p.169): for distinct `x, y ∈ dom f`, there exist `u ∈ supp⁺(x-y)` and
`v ∈ supp⁻(x-y)` with `f(x - χ_u + χ_v) ≤ f(x)` or `f(y + χ_u - χ_v) ≤ f(y)`. A function
`f : Zⱽ → R ∪ {+∞}` with `dom f ≠ ∅` satisfying this is **weakly quasi M-convex**. -/
def QMw {V : Type*} [Fintype V] [DecidableEq V] (f : (V → ℤ) → WithTop ℝ) : Prop :=
  ∀ x ∈ DomZ f, ∀ y ∈ DomZ f, x ≠ y → ∃ u ∈ SuppPos x y, ∃ v ∈ SuppNeg x y,
    f (fun w => x w - CharVec u w + CharVec v w) ≤ f x ∨
      f (fun w => y w + CharVec u w - CharVec v w) ≤ f y

end DiscreteConvex.MConvexFunctions.Quasi
