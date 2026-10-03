import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_IndicatorVec
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_SuppPos
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_SuppNeg

namespace DiscreteConvex.ConjugacyDualityB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Axiom (B-EXC[Z]): `B` is an M-convex set. -/
def ExchangeAxiomB (B : Set (V → ℤ)) : Prop :=
  ∀ x ∈ B, ∀ y ∈ B, ∀ u ∈ SuppPos x y, ∃ v ∈ SuppNeg x y,
    (fun w => x w - IndicatorVec {u} w + IndicatorVec {v} w) ∈ B ∧
    (fun w => y w + IndicatorVec {u} w - IndicatorVec {v} w) ∈ B

end DiscreteConvex.ConjugacyDualityB
