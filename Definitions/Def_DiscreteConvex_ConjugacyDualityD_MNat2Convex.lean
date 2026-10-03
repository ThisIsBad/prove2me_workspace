import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_MNaturalConvex

namespace DiscreteConvex.ConjugacyDualityD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `f` is M♮₂-convex: the sum of two M♮-convex functions. -/
def MNat2Convex (f : (V → ℤ) → WithTop ℝ) : Prop :=
  ∃ f1 f2 : (V → ℤ) → WithTop ℝ, MNaturalConvex f1 ∧ MNaturalConvex f2 ∧
    f = fun x => f1 x + f2 x

end DiscreteConvex.ConjugacyDualityD
