import Mathlib

namespace DiscreteConvex.ConjugacyDualityC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The positive support for integer vectors. -/
def SuppPos (x y : V → ℤ) : Finset V := Finset.univ.filter (fun v => y v < x v)

end DiscreteConvex.ConjugacyDualityC
