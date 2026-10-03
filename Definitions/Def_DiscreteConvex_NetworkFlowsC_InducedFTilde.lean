import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsC_BoundaryZ
import Definitions.Def_DiscreteConvex_NetworkFlowsC_ToEReal
import Definitions.Def_DiscreteConvex_NetworkFlowsC_SupportedOn

namespace DiscreteConvex.NetworkFlowsC

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- The flow-type induced function `f̃ : Zᵀ → Z∪{±∞}` of Eq. (9.81). -/
noncomputable def InducedFTilde (tail head : A → V) (S T : Finset V) (fa : A → ℤ → WithTop ℝ)
    (f : (V → ℤ) → WithTop ℝ) (y : V → ℤ) : EReal :=
  sInf {L : EReal | ∃ xi : A → ℤ, ∃ x : V → ℤ, SupportedOn S x ∧
    (∀ v ∈ S, BoundaryZ tail head xi v = x v) ∧
    (∀ v ∈ T, BoundaryZ tail head xi v = -(y v)) ∧
    (∀ v, v ∉ S → v ∉ T → BoundaryZ tail head xi v = 0) ∧
    L = ToEReal (f x + ∑ a : A, fa a (xi a))}

end DiscreteConvex.NetworkFlowsC
