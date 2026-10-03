import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.140, supporting Proposition 6.9, in `DiscreteConvex.MConvexFunctionsB`.
-/

namespace DiscreteConvex.MConvexFunctionsB

/-- The two-variable "conservation-law" lift of a univariate function: `f(x) = ψ(x(1))` if
`x(1)+x(2)=0`, else `+∞`. -/
def ConservationLift (psi : ℤ → WithTop ℝ) : (Fin 2 → ℤ) → WithTop ℝ :=
  fun x => if x 0 + x 1 = 0 then psi (x 0) else ⊤

end DiscreteConvex.MConvexFunctionsB
