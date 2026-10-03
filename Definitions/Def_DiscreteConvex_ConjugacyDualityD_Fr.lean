import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_F0

namespace DiscreteConvex.ConjugacyDualityD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The perturbation `Fr(x,u) = F0(x,u) + r(u)`, Eq. (8.61). -/
noncomputable def Fr (c r : (V → ℤ) → WithTop ℝ) (B : Set (V → ℤ)) (x u : V → ℤ) : WithTop ℝ :=
  F0 c B x u + r u

end DiscreteConvex.ConjugacyDualityD
