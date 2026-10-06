import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_ArgMin
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_M2Convex
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_MNat2Convex
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_M2ConvexSet
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_MNat2ConvexSet

namespace DiscreteConvex.ConjugacyDualityB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Proposition 8.30 (p.227). The minimizer set of an M2-(resp. M♮₂-)convex function is
M2-(resp. M♮₂-)convex, if nonempty. -/
theorem m2_convex_argmin_is_m2_convex_set :
    (∀ f : (V → ℤ) → WithTop ℝ, M2Convex f → (ArgMin f).Nonempty → M2ConvexSet (ArgMin f)) ∧
    (∀ f : (V → ℤ) → WithTop ℝ, MNat2Convex f → (ArgMin f).Nonempty → MNat2ConvexSet (ArgMin f)) := by sorry

end DiscreteConvex.ConjugacyDualityB

