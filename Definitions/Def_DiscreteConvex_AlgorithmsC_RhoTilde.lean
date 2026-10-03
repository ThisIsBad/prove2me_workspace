import Mathlib
import Definitions.Def_DiscreteConvex_AlgorithmsC_GammaSet

namespace DiscreteConvex.AlgorithmsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `ρ̃(Y) = ρ(Γ(Y)∪Z) - ρ(Z)`. -/
def RhoTilde {U : Type*} [DecidableEq U] (rho : Finset V → ℤ) (Gamma : U → Finset V) (Z : Finset V)
    (Y : Finset U) : ℤ :=
  rho (GammaSet Gamma Y ∪ Z) - rho Z

end DiscreteConvex.AlgorithmsC
