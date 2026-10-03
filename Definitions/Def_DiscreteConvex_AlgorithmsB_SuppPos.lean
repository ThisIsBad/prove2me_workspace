import Mathlib

namespace DiscreteConvex.AlgorithmsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
def SuppPos (x y : V → ℤ) : Finset V := Finset.univ.filter (fun v => y v < x v)

end DiscreteConvex.AlgorithmsB
