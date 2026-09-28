import Mathlib
import Definitions.Def_OnlinePrimalDual_Framework_CoveringInstance

namespace OnlinePrimalDual.Framework

/-- The accumulated dual value `∑_{j | i ∈ S(j)} yⱼ` charged against primal variable `i`'s
dual/packing constraint `∑_{j | i ∈ S(j)} yⱼ ≤ cᵢ` (Fig. 4.1, p. 116, PDF p. 27). Used both to
state packing feasibility/violation and, in Section 4.2's algorithms, as the argument to each
algorithm's update rule for `xᵢ`. -/
def dualSum {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    (inst : CoveringInstance I J) (y : J → ℝ) (i : I) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j => i ∈ inst.S j), y j

end OnlinePrimalDual.Framework
