import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_SBF
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_TRF
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_InfConv
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_InfConvE

namespace DiscreteConvex.ConjugacyDualityC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `g` is L2-convex: the integer infimal convolution of two L-convex functions, required (as the book does) to be `> -∞`:
`InfConv` takes its infimum in the conditionally complete `WithTop ℝ` and reads the junk value
`0` when the values are unbounded below. -/
def L2Convex (g : (V → ℤ) → WithTop ℝ) : Prop :=
  ∃ g1 g2 : (V → ℤ) → WithTop ℝ, (SBF g1 ∧ TRF g1) ∧ (SBF g2 ∧ TRF g2) ∧
    (∀ p, InfConvE g1 g2 p ≠ ⊥) ∧ g = InfConv g1 g2

end DiscreteConvex.ConjugacyDualityC
