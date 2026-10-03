import Mathlib
import Definitions.Def_DiscreteConvex_AlgorithmsB_PrefixUpTo
import Definitions.Def_DiscreteConvex_AlgorithmsB_PrefixBefore

namespace DiscreteConvex.AlgorithmsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The extreme base `y(v) = ρ(L(v)) - ρ(L(v)∖{v})` associated with a linear ordering `L`
(Eq. (10.12)). -/
def ExtremeBaseVec (rho : Finset V → ℤ) (L : V ≃ Fin (Fintype.card V)) (v : V) : ℤ :=
  rho (PrefixUpTo L v) - rho (PrefixBefore L v)

end DiscreteConvex.AlgorithmsB
