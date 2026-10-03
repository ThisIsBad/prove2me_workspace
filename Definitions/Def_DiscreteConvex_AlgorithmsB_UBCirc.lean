import Mathlib
import Definitions.Def_DiscreteConvex_AlgorithmsB_LB
import Definitions.Def_DiscreteConvex_AlgorithmsB_UB

namespace DiscreteConvex.AlgorithmsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `u°_B(v) = (1/n)ℓ_B(v) + (1-1/n)u_B(v)`. -/
noncomputable def UBCirc (B : Set (V → ℤ)) (v : V) : ℚ :=
  (1/(Fintype.card V : ℚ)) * (LB B v : ℚ) + (1 - 1/(Fintype.card V : ℚ)) * (UB B v : ℚ)

end DiscreteConvex.AlgorithmsB
