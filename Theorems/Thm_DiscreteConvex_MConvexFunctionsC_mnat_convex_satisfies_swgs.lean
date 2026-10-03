import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_MNaturalConvex
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_MNatSWGS


namespace DiscreteConvex.MConvexFunctionsC

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Proposition 6.35 (p.155). -/
theorem mnat_convex_satisfies_swgs (f : (V → ℤ) → WithTop ℝ) (hf : MNaturalConvex f) :
    MNatSWGS f := by sorry

end DiscreteConvex.MConvexFunctionsC
