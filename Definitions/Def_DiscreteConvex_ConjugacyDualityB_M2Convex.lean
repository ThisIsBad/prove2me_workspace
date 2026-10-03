import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_MExchangeAxiom

namespace DiscreteConvex.ConjugacyDualityB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `f` is M2-convex: the sum of two M-convex functions. -/
def M2Convex (f : (V → ℤ) → WithTop ℝ) : Prop :=
  ∃ f1 f2 : (V → ℤ) → WithTop ℝ, MExchangeAxiom f1 ∧ MExchangeAxiom f2 ∧
    f = fun x => f1 x + f2 x

end DiscreteConvex.ConjugacyDualityB
