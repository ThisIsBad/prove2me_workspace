import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsC_InducedFTildeRWT
import Definitions.Def_DiscreteConvex_NetworkFlowsC_ExtendFromTR

namespace DiscreteConvex.NetworkFlowsC

open Classical
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

/-- The real-domain induced function `f̃` as a function **on `Rᵀ`**, which is what Theorem 9.28
asserts is M-convex; read on all of `Rⱽ` it is a cylinder along `V ∖ T`. -/
noncomputable def InducedFTildeROnT (tail head : A → V) (S T : Finset V) (fa : A → ℝ → WithTop ℝ)
    (f : (V → ℝ) → WithTop ℝ) (y : {v // v ∈ T} → ℝ) : WithTop ℝ :=
  InducedFTildeRWT tail head S T fa f (ExtendFromTR T y)

end DiscreteConvex.NetworkFlowsC
