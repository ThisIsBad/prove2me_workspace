import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsC_InducedFTildeWT
import Definitions.Def_DiscreteConvex_NetworkFlowsC_ExtendFromT

namespace DiscreteConvex.NetworkFlowsC

open Classical
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

/-- The induced function `f̃` of Eq. (9.81) as a function **on `Zᵀ`**, which is what Theorems
9.26 and 9.27 assert is M-convex; `InducedFTildeWT` reads the same value off a vector of `Zⱽ` and
is therefore a cylinder along `V ∖ T`, for which the exchange axiom fails whenever `T ≠ V`. -/
noncomputable def InducedFTildeOnT (tail head : A → V) (S T : Finset V) (fa : A → ℤ → WithTop ℝ)
    (f : (V → ℤ) → WithTop ℝ) (y : {v // v ∈ T} → ℤ) : WithTop ℝ :=
  InducedFTildeWT tail head S T fa f (ExtendFromT T y)

end DiscreteConvex.NetworkFlowsC
