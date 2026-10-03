import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_DomZ
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_MNaturalConvex
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_ConvexExtensible
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_MNatSWGS


namespace DiscreteConvex.MConvexFunctionsC

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Theorem 6.36 (p.155). -/
theorem swgs_characterizes_mnat_convex (f : (V → ℤ) → WithTop ℝ) (hce : ConvexExtensible f)
    (hne : (DomZ f).Nonempty) : MNaturalConvex f ↔ MNatSWGS f := by sorry

end DiscreteConvex.MConvexFunctionsC
