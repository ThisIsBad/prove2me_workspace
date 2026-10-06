import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_MExchangeAxiom
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_DomZ
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_FCheck


/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.148, Proposition 6.25, in `DiscreteConvex.MConvexFunctionsB`.
-/

namespace DiscreteConvex.MConvexFunctionsB

/-- Proposition 6.25 (Murota, *Discrete Convex Analysis*, SIAM 2003, p.148). See the item's
`natural_language_statement` for the full statement. -/
theorem mconvex_subgradient_inequality {V : Type*} [Fintype V] [DecidableEq V]
    (f : (V → ℤ) → WithTop ℝ) (hf : MExchangeAxiom f) (x y : V → ℤ) (hx : x ∈ DomZ f)
    (hy : y ∈ DomZ f) :
    f y ≥ f x + FCheck f x y := by sorry

end DiscreteConvex.MConvexFunctionsB

