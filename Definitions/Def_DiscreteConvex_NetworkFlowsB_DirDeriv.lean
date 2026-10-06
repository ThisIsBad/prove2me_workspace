import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsB_PosScalarMul

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- The directional derivative `f'(x;d) = inf_{t>0} (f(x+td)-f(x))/t`. -/
noncomputable def DirDeriv (f : (V → ℝ) → WithTop ℝ) (x d : V → ℝ) : WithTop ℝ :=
  sInf {L : WithTop ℝ | ∃ t : ℝ, 0 < t ∧
    L = PosScalarMul (1 / t) (f (fun v => x v + t * d v) - f x)}

end DiscreteConvex.NetworkFlowsB
