import Mathlib

namespace DiscreteConvex.MConvexFunctionsE

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The linear-weighted function `f[p](x) = f(x) - ⟨p,x⟩`. -/
def LinearWeight (f : (V → ℤ) → WithTop ℝ) (p : V → ℝ) : (V → ℤ) → WithTop ℝ :=
  fun x => f x + (((-(∑ v, p v * (x v : ℝ)) : ℝ)) : WithTop ℝ)

end DiscreteConvex.MConvexFunctionsE
