import Mathlib

namespace DiscreteConvex.AlgorithmsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `X` minimizes the `WithTop ℝ`-valued set function `ρ`. -/
def IsMinimizerOfWT (rho : Finset V → WithTop ℝ) (W : Finset V) : Prop := ∀ X, rho W ≤ rho X

end DiscreteConvex.AlgorithmsC
