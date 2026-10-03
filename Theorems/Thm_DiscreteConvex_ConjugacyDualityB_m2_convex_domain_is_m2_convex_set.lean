import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_DomZ
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_M2Convex
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_MNat2Convex
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_M2ConvexSet
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_MNat2ConvexSet

namespace DiscreteConvex.ConjugacyDualityB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Proposition 8.29 (p.227). The effective domain of an M2-(resp. M♮₂-)convex function is
M2-(resp. M♮₂-)convex. -/
theorem m2_convex_domain_is_m2_convex_set :
    (∀ f : (V → ℤ) → WithTop ℝ, M2Convex f → M2ConvexSet (DomZ f)) ∧
    (∀ f : (V → ℤ) → WithTop ℝ, MNat2Convex f → MNat2ConvexSet (DomZ f)) := by sorry

end DiscreteConvex.ConjugacyDualityB
