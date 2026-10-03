import Mathlib
import Definitions.Def_DiscreteConvex_AlgorithmsC_FromEReal
import Definitions.Def_DiscreteConvex_AlgorithmsC_ConjugateScalingE

namespace DiscreteConvex.AlgorithmsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `f⟨α⟩ = ConjugateFromZ(g_α)`, the conjugate scaling of `f` with scaling factor `α`, Eq.
(10.77). -/
noncomputable def ConjugateScaling (g : (V → ℤ) → WithTop ℝ) (alpha : ℤ) (x : V → ℝ) : WithTop ℝ :=
  FromEReal (ConjugateScalingE g alpha x)

-- ===== Theorems =====

end DiscreteConvex.AlgorithmsC
