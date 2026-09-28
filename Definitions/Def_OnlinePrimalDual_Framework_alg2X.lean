import Mathlib
import Definitions.Def_OnlinePrimalDual_Framework_CoveringInstance
import Definitions.Def_OnlinePrimalDual_Framework_dualSum

namespace OnlinePrimalDual.Framework

/-- The final value Algorithm 2 (the continuous algorithm, p. 121, PDF p. 32) assigns to primal
variable `xᵢ`: `xᵢ = (1/d)(exp((ln(1+d)/cᵢ) · ∑_{j | i ∈ S(j)} yⱼ) − 1)`, exactly the update
function stated in Algorithm 2's step (1b), evaluated at the final accumulated dual sum
`dualSum inst y i` (the exponential only ever depends on dual variables of constraints already
revealed, since `y` is `0` on constraints not yet arrived). -/
noncomputable def alg2X {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    (inst : CoveringInstance I J) (y : J → ℝ) (i : I) : ℝ :=
  (1 / inst.d) * (Real.exp (Real.log (1 + inst.d) / inst.c i * dualSum inst y i) - 1)

end OnlinePrimalDual.Framework
