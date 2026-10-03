import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_LiftedFunction
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_MExchangeAxiom

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.134, in `DiscreteConvex.MConvexFunctionsB`.
-/

namespace DiscreteConvex.MConvexFunctionsB

/-- `f : Zⱽ → R ∪ {+∞}` is **M♮-convex**: its lift `f̃` (Eq. (6.4)) is an M-convex function. -/
def MNaturalConvex {V : Type*} [Fintype V] [DecidableEq V] (f : (V → ℤ) → WithTop ℝ) : Prop :=
  MExchangeAxiom (LiftedFunction f)

end DiscreteConvex.MConvexFunctionsB
