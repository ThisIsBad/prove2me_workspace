import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.98, Eq. (3.69), reused pp.143,147-148, in `DiscreteConvex.MConvexFunctionsB`.
-/

namespace DiscreteConvex.MConvexFunctionsB

/-- The linear-weighted function `f[p](x) = f(x) - ⟨p,x⟩`, Eq. (3.69). -/
def LinearWeight {V : Type*} [Fintype V] (f : (V → ℤ) → WithTop ℝ) (p : V → ℝ) : (V → ℤ) → WithTop ℝ :=
  fun x => f x + (((-(∑ v, p v * (x v : ℝ)) : ℝ)) : WithTop ℝ)

end DiscreteConvex.MConvexFunctionsB
