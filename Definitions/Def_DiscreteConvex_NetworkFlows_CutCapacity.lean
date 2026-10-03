import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlows_DeltaPlus
import Definitions.Def_DiscreteConvex_NetworkFlows_DeltaMinus
import Definitions.Def_DiscreteConvex_NetworkFlows_UpperCapOf
import Definitions.Def_DiscreteConvex_NetworkFlows_NegLowerCapOf

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.247, Eq. (9.16): the cut capacity function,
in `DiscreteConvex.NetworkFlows`.
-/

namespace DiscreteConvex.NetworkFlows

/-- The **cut capacity function** `κ(X) = c̄(Δ⁺X) - c(Δ⁻X)` (Eq. (9.16)). -/
noncomputable def CutCapacity {V A : Type*} [Fintype A] [DecidableEq V]
    (tail head : A → V) (cUpper : A → WithTop ℝ) (cLower : A → WithBot ℝ) (X : Finset V) :
    WithTop ℝ :=
  UpperCapOf cUpper (DeltaPlus tail head X) + NegLowerCapOf cLower (DeltaMinus tail head X)

end DiscreteConvex.NetworkFlows
