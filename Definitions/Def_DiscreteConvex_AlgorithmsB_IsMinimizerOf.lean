import Mathlib

namespace DiscreteConvex.AlgorithmsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `X` minimizes `ρ`. -/
def IsMinimizerOf (rho : Finset V → ℤ) (W : Finset V) : Prop := ∀ X, rho W ≤ rho X

end DiscreteConvex.AlgorithmsB
