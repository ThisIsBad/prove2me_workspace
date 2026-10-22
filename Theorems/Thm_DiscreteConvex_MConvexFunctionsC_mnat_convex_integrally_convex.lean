import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_MNaturalConvex
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_ConvexExtensible
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_IsIntegrallyConvexFunction


namespace DiscreteConvex.MConvexFunctionsC

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Theorem 6.42 (p.159). -/
theorem mnat_convex_integrally_convex (f : (V → ℤ) → WithTop ℝ) (hf : MNaturalConvex f) :
    IsIntegrallyConvexFunction f ∧ ConvexExtensible f := by sorry

end DiscreteConvex.MConvexFunctionsC

