import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsC_ToEReal
import Definitions.Def_DiscreteConvex_NetworkFlowsC_SupportedOnR

namespace DiscreteConvex.NetworkFlowsC

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
noncomputable def InducedGTildeR (tail head : A → V) (S T : Finset V) (ga : A → ℝ → WithTop ℝ)
    (g : (V → ℝ) → WithTop ℝ) (q : V → ℝ) : EReal :=
  sInf {L : EReal | ∃ eta : A → ℝ, ∃ P : V → ℝ, ∃ p : V → ℝ, SupportedOnR S p ∧
    (∀ v ∈ S, P v = p v) ∧ (∀ v ∈ T, P v = q v) ∧
    (∀ a : A, eta a = -(P (tail a) - P (head a))) ∧
    L = ToEReal (g p + ∑ a : A, ga a (eta a))}

end DiscreteConvex.NetworkFlowsC
