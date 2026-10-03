import Mathlib

namespace DiscreteConvex.LConvexFunctionsD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The distinct values of `p : V → R`, sorted in decreasing order. -/
noncomputable def SortedValues (p : V → ℝ) : List ℝ :=
  (Finset.image p Finset.univ).sort (· ≥ ·)

end DiscreteConvex.LConvexFunctionsD
