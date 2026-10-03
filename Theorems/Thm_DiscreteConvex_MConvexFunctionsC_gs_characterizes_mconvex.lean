import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_DomZ
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_MExchangeAxiom
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_MNaturalConvex
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_ConvexExtensible
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_MGS
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_MNatGS


namespace DiscreteConvex.MConvexFunctionsC

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Theorem 6.34 (p.154). -/
theorem gs_characterizes_mconvex (f : (V → ℤ) → WithTop ℝ) (hce : ConvexExtensible f)
    (hne : (DomZ f).Nonempty) (hbdd : (DomZ f).Finite) :
    ((∃ r : ℤ, ∀ x ∈ DomZ f, ∑ v, x v = r) → (MExchangeAxiom f ↔ MGS f)) ∧
    (MNaturalConvex f ↔ MNatGS f) := by sorry

end DiscreteConvex.MConvexFunctionsC
