import Mathlib

namespace DiscreteConvex.MConvexFunctionsC

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The integral neighborhood `N(x)` of `x ∈ Rⱽ`, as a `Finset`. -/
noncomputable def IntegralNeighborhoodFinset (x : V → ℝ) : Finset (V → ℤ) :=
  Fintype.piFinset (fun v => Finset.Icc ⌊x v⌋ ⌈x v⌉)

end DiscreteConvex.MConvexFunctionsC
