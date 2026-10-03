import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_CharVec

namespace DiscreteConvex.MConvexFunctionsE

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The directional difference `Δf(z; v, u) = f(z + χ_v - χ_u) - f(z)`, Eq. (6.1) notation. -/
noncomputable def DeltaF (f : (V → ℤ) → WithTop ℝ) (z : V → ℤ) (v u : V) : WithTop ℝ :=
  f (fun w => z w + CharVec v w - CharVec u w) - f z

end DiscreteConvex.MConvexFunctionsE
