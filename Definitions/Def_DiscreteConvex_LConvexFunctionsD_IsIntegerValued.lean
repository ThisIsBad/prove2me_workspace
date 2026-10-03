import Mathlib

namespace DiscreteConvex.LConvexFunctionsD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `ρ : 2^V → R∪{+∞}` is integer valued. -/
def IsIntegerValued (rho : Finset V → WithTop ℝ) : Prop := ∀ X, ∃ k : ℤ, rho X = ((k : ℝ) : WithTop ℝ)

end DiscreteConvex.LConvexFunctionsD
