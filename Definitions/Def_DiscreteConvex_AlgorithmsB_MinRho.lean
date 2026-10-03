import Mathlib

namespace DiscreteConvex.AlgorithmsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `min{ρ(X) | X ⊆ V}`. -/
def MinRho (rho : Finset V → ℤ) : ℤ :=
  (Finset.univ : Finset (Finset V)).inf' ⟨∅, Finset.mem_univ _⟩ rho

end DiscreteConvex.AlgorithmsB
