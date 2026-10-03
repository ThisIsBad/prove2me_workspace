import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_IndicatorWT

namespace DiscreteConvex.ConjugacyDualityD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The perturbation `F0(x,u) = c(x) + δ_B(x+u)`, Eq. (8.62). -/
noncomputable def F0 (c : (V → ℤ) → WithTop ℝ) (B : Set (V → ℤ)) (x u : V → ℤ) : WithTop ℝ :=
  c x + IndicatorWT B (fun v => x v + u v)

end DiscreteConvex.ConjugacyDualityD
