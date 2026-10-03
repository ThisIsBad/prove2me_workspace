import Mathlib

namespace DiscreteConvex.LConvexFunctionsD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The subdifferential `∂_R g(p)` of a real-domain function at a real point. -/
def SubDifferentialR (g : (V → ℝ) → WithTop ℝ) (p : V → ℝ) : Set (V → ℝ) :=
  {x : V → ℝ | ∀ q : V → ℝ, g q - g p ≥ (((∑ v, x v * (q v - p v)) : ℝ) : WithTop ℝ)}

end DiscreteConvex.LConvexFunctionsD
