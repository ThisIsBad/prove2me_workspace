import Mathlib
import Definitions.Def_DiscreteConvex_AlgorithmsC_IsMinimizerOfWT

namespace DiscreteConvex.AlgorithmsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `W` is the *minimal* minimizer of `ρ`: a minimizer contained in every other minimizer. -/
def IsMinimalMinimizerWT (rho : Finset V → WithTop ℝ) (W : Finset V) : Prop :=
  IsMinimizerOfWT rho W ∧ ∀ W', IsMinimizerOfWT rho W' → W ⊆ W'

end DiscreteConvex.AlgorithmsC
