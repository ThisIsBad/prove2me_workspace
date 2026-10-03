import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_DomR
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_SBFR
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_TRFR
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_ZeroLR
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_LinearWeightR
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_ArgMinR
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_MConvexPolyhedronR
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_LConvexPolyhedronR
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_DirDeriv
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_SubDifferentialR

namespace DiscreteConvex.LConvexFunctionsD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Theorem 7.45 (p.197-198). GOAL. Four characterizations of polyhedral L-convexity: via the
exchange-style axioms, positively-homogeneous directional derivatives, M-convex subdifferentials,
and L-convex weighted-minimizer polyhedra. (c) and (d) are in the real classes `M⁰[R]` and
`L⁰[R]`, which are not integral: `g(p) = (1/2) max(p₁ - p₂, 0)` satisfies (a) with
subdifferential the segment from `(0,0)` to `(1/2,-1/2)` at `0`, and `g(p) = max(p₁ - p₂ - 1/2, 0)`
satisfies (a) with minimizer set `{p : p₁ - p₂ ≤ 1/2}`; neither is the convex hull of an integer
set. -/
theorem polyhedral_lconvex_four_characterizations (g : (V → ℝ) → WithTop ℝ)
    (hdom : (DomR g).Nonempty) :
    [SBFR g ∧ TRFR g,
     ∀ p ∈ DomR g, ZeroLR (fun d => DirDeriv g p d),
     ∀ p ∈ DomR g, MConvexPolyhedronR (SubDifferentialR g p),
     ∀ x : V → ℝ, (ArgMinR (LinearWeightR g (fun v => - x v))).Nonempty →
        LConvexPolyhedronR (ArgMinR (LinearWeightR g (fun v => - x v)))].TFAE := by sorry

end DiscreteConvex.LConvexFunctionsD
