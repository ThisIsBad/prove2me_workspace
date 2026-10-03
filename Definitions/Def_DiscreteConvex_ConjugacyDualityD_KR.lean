import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_ToEReal
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_Fr

namespace DiscreteConvex.ConjugacyDualityD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The `r`-regularized Lagrangian function `Kr(x,y) = inf_u [Fr(x,u)+⟨u,y⟩]`, Eq. (8.64). -/
noncomputable def KR (c r : (V → ℤ) → WithTop ℝ) (B : Set (V → ℤ)) (x y : V → ℤ) : EReal :=
  sInf {t : EReal | ∃ u : V → ℤ,
    t = ToEReal (Fr c r B x u) + ((∑ i, (u i : ℝ) * (y i : ℝ) : ℝ) : EReal)}

end DiscreteConvex.ConjugacyDualityD
