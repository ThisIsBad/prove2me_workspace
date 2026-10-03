import Mathlib
import Definitions.Def_DiscreteConvex_AlgorithmsC_ConjugateFromZE
import Definitions.Def_DiscreteConvex_AlgorithmsC_ScaledConjugate

namespace DiscreteConvex.AlgorithmsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `f⟨α⟩`, `EReal`-valued, Eq. (10.77). -/
noncomputable def ConjugateScalingE (g : (V → ℤ) → WithTop ℝ) (alpha : ℤ) (x : V → ℝ) : EReal :=
  ConjugateFromZE (ScaledConjugate g alpha) x

end DiscreteConvex.AlgorithmsC
