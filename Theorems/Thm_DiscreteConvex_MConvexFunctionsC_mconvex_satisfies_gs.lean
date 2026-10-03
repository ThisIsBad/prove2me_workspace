import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_MExchangeAxiom
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_MGS


namespace DiscreteConvex.MConvexFunctionsC

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Proposition 6.32 (p.153). -/
theorem mconvex_satisfies_gs (f : (V → ℤ) → WithTop ℝ) (hf : MExchangeAxiom f) : MGS f := by sorry

end DiscreteConvex.MConvexFunctionsC
