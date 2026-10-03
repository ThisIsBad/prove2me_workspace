import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_IsPolyhedronW
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_SBFR
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_TRFR

namespace DiscreteConvex.LConvexFunctionsD

open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The class `L⁰[R]` of **real** L-convex polyhedra: a polyhedron whose indicator satisfies
(SBF[R]) and (TRF[R]), i.e. a polyhedron closed under `⊔`, `⊓` and translation by the all-ones
vector. `LConvexPolyhedron` is the convex hull of an integer L-convex set, i.e. the *integral*
class `L⁰[Z|R]`. Theorem 7.45 (d) concludes in the real class: the minimizer set of
`g(p) = max(p₁ - p₂ - 1/2, 0)` is `{p : p₁ - p₂ ≤ 1/2}`, the convex hull of no integer set. -/
noncomputable def LConvexPolyhedronR (P : Set (V → ℝ)) : Prop :=
  IsPolyhedronW P ∧
    SBFR (fun p => if p ∈ P then (0 : WithTop ℝ) else ⊤) ∧
    TRFR (fun p => if p ∈ P then (0 : WithTop ℝ) else ⊤)

end DiscreteConvex.LConvexFunctionsD
