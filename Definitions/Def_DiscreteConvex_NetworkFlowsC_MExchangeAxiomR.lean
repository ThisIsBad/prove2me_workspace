import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsC_DomR
import Definitions.Def_DiscreteConvex_NetworkFlowsC_SuppPosR
import Definitions.Def_DiscreteConvex_NetworkFlowsC_SuppNegR

namespace DiscreteConvex.NetworkFlowsC

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- Axiom (M-EXC[R]). -/
def MExchangeAxiomR (g : (V → ℝ) → WithTop ℝ) : Prop :=
  ∀ x ∈ DomR g, ∀ y ∈ DomR g, ∀ u ∈ SuppPosR x y, ∃ v ∈ SuppNegR x y, ∃ alpha0 : ℝ, 0 < alpha0 ∧
    ∀ alpha : ℝ, 0 ≤ alpha → alpha ≤ alpha0 →
      g x + g y ≥
        g (fun w => x w - alpha * (if w = u then (1:ℝ) else 0) + alpha * (if w = v then (1:ℝ) else 0)) +
        g (fun w => y w + alpha * (if w = u then (1:ℝ) else 0) - alpha * (if w = v then (1:ℝ) else 0))

end DiscreteConvex.NetworkFlowsC
