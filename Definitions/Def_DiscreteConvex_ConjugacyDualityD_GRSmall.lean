import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_KR

namespace DiscreteConvex.ConjugacyDualityD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The `r`-regularized dual objective `gr(y) = inf_x Kr(x,y)`, Eq. (8.65). -/
noncomputable def GRSmall (c r : (V → ℤ) → WithTop ℝ) (B : Set (V → ℤ)) (y : V → ℤ) : EReal :=
  sInf {t : EReal | ∃ x : V → ℤ, t = KR c r B x y}

end DiscreteConvex.ConjugacyDualityD
