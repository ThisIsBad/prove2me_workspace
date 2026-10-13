import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_FromEReal
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_ConvexConjugateR

namespace DiscreteConvex.ConjugacyDualityB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `f•`, projected back to `WithTop ℝ`. -/
noncomputable def ConvexConjugateRW (f : (V → ℝ) → WithTop ℝ) (p : V → ℝ) : WithTop ℝ :=
  FromEReal (ConvexConjugateR f p)

end DiscreteConvex.ConjugacyDualityB
