import Mathlib

namespace DiscreteConvex.LConvexFunctionsD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `g` is integer valued. -/
def IsIntegerValuedFn (g : (V → ℤ) → WithTop ℝ) : Prop := ∀ p, ∃ k : ℤ, g p = ((k : ℝ) : WithTop ℝ)

end DiscreteConvex.LConvexFunctionsD
