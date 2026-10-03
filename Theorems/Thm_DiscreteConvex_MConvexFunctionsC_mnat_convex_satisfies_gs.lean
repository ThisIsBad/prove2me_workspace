import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_MNaturalConvex
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_MNatGS


namespace DiscreteConvex.MConvexFunctionsC

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Proposition 6.33 (p.154). -/
theorem mnat_convex_satisfies_gs (f : (V → ℤ) → WithTop ℝ) (hf : MNaturalConvex f) : MNatGS f := by sorry

end DiscreteConvex.MConvexFunctionsC
