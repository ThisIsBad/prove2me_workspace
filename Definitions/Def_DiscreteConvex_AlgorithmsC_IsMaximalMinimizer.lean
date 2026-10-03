import Mathlib
import Definitions.Def_DiscreteConvex_AlgorithmsC_IsMinimizerOf

namespace DiscreteConvex.AlgorithmsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `W` is the maximal minimizer of `ρ`. -/
def IsMaximalMinimizer (rho : Finset V → ℤ) (W : Finset V) : Prop :=
  IsMinimizerOf rho W ∧ ∀ W', IsMinimizerOf rho W' → W' ⊆ W

end DiscreteConvex.AlgorithmsC
