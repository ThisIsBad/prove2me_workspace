import Mathlib
import Definitions.Def_DiscreteConvex_AlgorithmsC_PosScalarMul

namespace DiscreteConvex.AlgorithmsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `g_α(p) = g(αp)/α`, the conjugate-scaled dual function. -/
noncomputable def ScaledConjugate (g : (V → ℤ) → WithTop ℝ) (alpha : ℤ) (p : V → ℤ) : WithTop ℝ :=
  PosScalarMul (1/(alpha : ℝ)) (g (fun v => alpha * p v))

end DiscreteConvex.AlgorithmsC
