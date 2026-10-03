import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_CharVec
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_SuppPos
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_SuppNeg

namespace DiscreteConvex.MConvexFunctionsE

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `min_{u ∈ supp+(x-y)} min_{v ∈ supp-(x-y)} f(x - χ_u + χ_v)`, the common RHS of (6.94)/(6.97). -/
noncomputable def MinDown (f : (V → ℤ) → WithTop ℝ) (x y : V → ℤ) : WithTop ℝ :=
  (SuppPos x y).inf (fun u => (SuppNeg x y).inf (fun v =>
    f (fun w => x w - CharVec u w + CharVec v w)))

end DiscreteConvex.MConvexFunctionsE
