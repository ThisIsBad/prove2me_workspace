import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.140, supporting Proposition 6.9, in `DiscreteConvex.MConvexFunctionsB`.
-/

namespace DiscreteConvex.MConvexFunctionsB

/-- A univariate function viewed as a function of one `Unit`-indexed coordinate. -/
def UnivToFunc (psi : ℤ → WithTop ℝ) : (Unit → ℤ) → WithTop ℝ := fun x => psi (x ())

end DiscreteConvex.MConvexFunctionsB
