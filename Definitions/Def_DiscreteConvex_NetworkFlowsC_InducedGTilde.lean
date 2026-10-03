import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsC_ToEReal
import Definitions.Def_DiscreteConvex_NetworkFlowsC_SupportedOn

namespace DiscreteConvex.NetworkFlowsC

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- The potential-type induced function `g̃ : Zᵀ → Z∪{±∞}` of Eq. (9.82). -/
noncomputable def InducedGTilde (tail head : A → V) (S T : Finset V) (ga : A → ℤ → WithTop ℝ)
    (g : (V → ℤ) → WithTop ℝ) (q : V → ℤ) : EReal :=
  sInf {L : EReal | ∃ eta : A → ℤ, ∃ P : V → ℤ, ∃ p : V → ℤ, SupportedOn S p ∧
    (∀ v ∈ S, P v = p v) ∧ (∀ v ∈ T, P v = q v) ∧
    (∀ a : A, eta a = -(P (tail a) - P (head a))) ∧
    L = ToEReal (g p + ∑ a : A, ga a (eta a))}

end DiscreteConvex.NetworkFlowsC
