import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_MNaturalConvex
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_LNaturalConvex
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_MNat2Convex
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_LNat2Convex
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_IsSeparableConvex

namespace DiscreteConvex.ConjugacyDualityD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Theorem 8.49 (p.234). A function is both M♮₂- and L♮₂-convex iff it is both M♮- and
L♮-convex iff it is separable convex. -/
theorem separable_convex_iff_m2_and_l2 (f : (V → ℤ) → WithTop ℝ) :
    [MNat2Convex f ∧ LNat2Convex f, MNaturalConvex f ∧ LNaturalConvex f,
        IsSeparableConvex f].TFAE := by sorry

end DiscreteConvex.ConjugacyDualityD
