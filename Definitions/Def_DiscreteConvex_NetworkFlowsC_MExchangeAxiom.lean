import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsC_DomZ
import Definitions.Def_DiscreteConvex_NetworkFlowsC_SuppPos
import Definitions.Def_DiscreteConvex_NetworkFlowsC_SuppNeg

namespace DiscreteConvex.NetworkFlowsC

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- Axiom (M-EXC[Z]). -/
def MExchangeAxiom (f : (V → ℤ) → WithTop ℝ) : Prop :=
  ∀ x ∈ DomZ f, ∀ y ∈ DomZ f, ∀ u ∈ SuppPos x y, ∃ v ∈ SuppNeg x y,
    f x + f y ≥
      f (fun w => x w - (if w = u then (1:ℤ) else 0) + (if w = v then (1:ℤ) else 0)) +
      f (fun w => y w + (if w = u then (1:ℤ) else 0) - (if w = v then (1:ℤ) else 0))

end DiscreteConvex.NetworkFlowsC
