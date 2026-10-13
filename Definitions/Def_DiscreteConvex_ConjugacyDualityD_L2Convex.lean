import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_SBF
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_TRF
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_InfConv

namespace DiscreteConvex.ConjugacyDualityD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `g` is L2-convex: the integer infimal convolution of two L-convex functions. -/
def L2Convex (g : (V → ℤ) → WithTop ℝ) : Prop :=
  ∃ g1 g2 : (V → ℤ) → WithTop ℝ, (SBF g1 ∧ TRF g1) ∧ (SBF g2 ∧ TRF g2) ∧ g = InfConv g1 g2

end DiscreteConvex.ConjugacyDualityD
