import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_PosScalarMul

namespace DiscreteConvex.LConvexFunctionsD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The directional derivative `g'(p;d) = inf_{t>0}(g(p+td)-g(p))/t`. -/
noncomputable def DirDeriv (g : (V → ℝ) → WithTop ℝ) (p d : V → ℝ) : WithTop ℝ :=
  sInf {L : WithTop ℝ | ∃ t : ℝ, 0 < t ∧
    L = PosScalarMul (1 / t) (g (fun v => p v + t * d v) - g p)}

end DiscreteConvex.LConvexFunctionsD
