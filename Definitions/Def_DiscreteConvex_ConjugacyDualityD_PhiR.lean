import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_ToEReal
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_Fr

namespace DiscreteConvex.ConjugacyDualityD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The `r`-regularized optimal value function `φr(u) = inf_x Fr(x,u)`, Eq. (8.63). -/
noncomputable def PhiR (c r : (V → ℤ) → WithTop ℝ) (B : Set (V → ℤ)) (u : V → ℤ) : EReal :=
  sInf {t : EReal | ∃ x : V → ℤ, t = ToEReal (Fr c r B x u)}

end DiscreteConvex.ConjugacyDualityD
