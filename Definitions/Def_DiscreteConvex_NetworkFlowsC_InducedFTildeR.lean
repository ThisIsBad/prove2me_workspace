import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsC_Boundary
import Definitions.Def_DiscreteConvex_NetworkFlowsC_ToEReal
import Definitions.Def_DiscreteConvex_NetworkFlowsC_SupportedOnR

namespace DiscreteConvex.NetworkFlowsC

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
noncomputable def InducedFTildeR (tail head : A → V) (S T : Finset V) (fa : A → ℝ → WithTop ℝ)
    (f : (V → ℝ) → WithTop ℝ) (y : V → ℝ) : EReal :=
  sInf {L : EReal | ∃ xi : A → ℝ, ∃ x : V → ℝ, SupportedOnR S x ∧
    (∀ v ∈ S, Boundary tail head xi v = x v) ∧
    (∀ v ∈ T, Boundary tail head xi v = -(y v)) ∧
    (∀ v, v ∉ S → v ∉ T → Boundary tail head xi v = 0) ∧
    L = ToEReal (f x + ∑ a : A, fa a (xi a))}

end DiscreteConvex.NetworkFlowsC
