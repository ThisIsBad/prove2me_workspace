import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_MExchangeAxiom
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_DomZ
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_SuppPos
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_SuppNeg
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_CharVec


/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.147, Proposition 6.23, in `DiscreteConvex.MConvexFunctionsB`.
-/

namespace DiscreteConvex.MConvexFunctionsB

/-- Proposition 6.23 (Murota, *Discrete Convex Analysis*, SIAM 2003, p.147). See the item's
`natural_language_statement` for the full statement. -/
theorem mconvex_descent_direction {V : Type*} [Fintype V] [DecidableEq V]
    (f : (V → ℤ) → WithTop ℝ) (hf : MExchangeAxiom f) (x y : V → ℤ) (hx : x ∈ DomZ f)
    (hy : y ∈ DomZ f) (hgt : f x > f y) :
    f x > (SuppPos x y).inf (fun u => (SuppNeg x y).inf (fun v =>
      f (fun w => x w - CharVec u w + CharVec v w))) := by sorry

end DiscreteConvex.MConvexFunctionsB
