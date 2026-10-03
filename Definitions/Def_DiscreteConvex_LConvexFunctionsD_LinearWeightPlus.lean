import Mathlib

namespace DiscreteConvex.LConvexFunctionsD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `g[x](p) = g(p) + ⟨p,x⟩`, the L-side linear perturbation convention. -/
def LinearWeightPlus (g : (V → ℤ) → WithTop ℝ) (x : V → ℝ) : (V → ℤ) → WithTop ℝ :=
  fun p => g p + (((∑ v, x v * (p v : ℝ) : ℝ)) : WithTop ℝ)

end DiscreteConvex.LConvexFunctionsD
