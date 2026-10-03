import Mathlib

namespace DiscreteConvex.AlgorithmsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The `ℓ¹`-norm of an integer vector. -/
def L1Norm {W : Type*} [Fintype W] (x : W → ℤ) : ℤ := ∑ v, |x v|

end DiscreteConvex.AlgorithmsC
