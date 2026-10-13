import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_ToEReal

namespace DiscreteConvex.ConjugacyDualityB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The real Legendre-Fenchel transform of a real-domain function. -/
noncomputable def ConvexConjugateR (f : (V → ℝ) → WithTop ℝ) (p : V → ℝ) : EReal :=
  sSup {v : EReal | ∃ x : V → ℝ, v = ((∑ i, p i * x i : ℝ) : EReal) - ToEReal (f x)}

end DiscreteConvex.ConjugacyDualityB
