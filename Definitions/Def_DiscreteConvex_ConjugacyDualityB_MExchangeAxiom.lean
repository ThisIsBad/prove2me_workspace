import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_IndicatorVec
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_DomZ
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_SuppPos
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_SuppNeg

namespace DiscreteConvex.ConjugacyDualityB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Axiom (M-EXC[Z]): `f` is an M-convex function. -/
def MExchangeAxiom (f : (V → ℤ) → WithTop ℝ) : Prop :=
  ∀ x ∈ DomZ f, ∀ y ∈ DomZ f, ∀ u ∈ SuppPos x y, ∃ v ∈ SuppNeg x y,
    f x + f y ≥ f (fun w => x w - IndicatorVec {u} w + IndicatorVec {v} w) +
      f (fun w => y w + IndicatorVec {u} w - IndicatorVec {v} w)

end DiscreteConvex.ConjugacyDualityB
