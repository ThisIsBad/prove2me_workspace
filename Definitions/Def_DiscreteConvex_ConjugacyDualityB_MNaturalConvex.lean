import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_MExchangeAxiom
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_LiftedFunction

namespace DiscreteConvex.ConjugacyDualityB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `f` is M♮-convex: its lift is M-convex. -/
def MNaturalConvex (f : (V → ℤ) → WithTop ℝ) : Prop := MExchangeAxiom (LiftedFunction f)

end DiscreteConvex.ConjugacyDualityB
