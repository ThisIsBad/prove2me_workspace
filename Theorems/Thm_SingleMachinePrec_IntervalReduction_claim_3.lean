import Mathlib
import Definitions.Def_SingleMachinePrec_IntervalReduction_TreeLayout
import Definitions.Def_SingleMachinePrec_IntervalReduction_Instance

namespace SingleMachinePrec.IntervalReduction

/-- Claim 3 (p. 663): the subgraph `G′_I = (D, E_I)` of `G^S_I` induced by `D` is isomorphic
to `G′`. -/
theorem claim_3 {N : ℕ} {G : SimpleGraph (Fin N)} (L : TreeLayout G) :
    Nonempty (GIprime L ≃g GPrime L) := by sorry

end SingleMachinePrec.IntervalReduction

