import Mathlib

namespace DiscreteConvex.MConvexFunctionsC

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `f[p](x) = f(x) - ⟨p,x⟩`. -/
def LinearWeight (f : (V → ℤ) → WithTop ℝ) (p : V → ℝ) : (V → ℤ) → WithTop ℝ :=
  fun x => f x + (((-(∑ v, p v * (x v : ℝ)) : ℝ)) : WithTop ℝ)

end DiscreteConvex.MConvexFunctionsC
