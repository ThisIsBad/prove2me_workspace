import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_LNaturalConvex
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_InfConv

namespace DiscreteConvex.ConjugacyDualityD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `g` is L♮₂-convex: the integer infimal convolution of two L♮-convex functions. -/
def LNat2Convex (g : (V → ℤ) → WithTop ℝ) : Prop :=
  ∃ g1 g2 : (V → ℤ) → WithTop ℝ, LNaturalConvex g1 ∧ LNaturalConvex g2 ∧ g = InfConv g1 g2

end DiscreteConvex.ConjugacyDualityD
