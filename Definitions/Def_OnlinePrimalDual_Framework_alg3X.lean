import Mathlib
import Definitions.Def_OnlinePrimalDual_Framework_CoveringInstance
import Definitions.Def_OnlinePrimalDual_Framework_dualSum

namespace OnlinePrimalDual.Framework

/-- The final value Algorithm 3 (the complementary-slackness algorithm, p. 124, PDF p. 35)
assigns to primal variable `xᵢ`. Step (1b) sets `xᵢ ← 1/d` exactly when
`∑_{j | i ∈ S(j)} yⱼ` first reaches `cᵢ`; step (1c) then continuously updates `xᵢ` (while
`1/d ≤ xᵢ < 1`) by `xᵢ ← (1/d)exp((∑_{j | i ∈ S(j)} yⱼ)/cᵢ − 1)`. Since `dualSum inst y i` is
monotone non-decreasing in the process and this closed form is monotone in `dualSum`, evaluating
it at the *final* accumulated sum and capping at `1` (`min 1 …`, matching the book's own proof of
claim (2), p. 125, "the corresponding variable xᵢ cannot exceed 1") reproduces the same final
value as the step-by-step process, including its freeze once `xᵢ = 1`; before activation
(`dualSum inst y i < cᵢ`) the variable has not yet been touched by step (1b) and is `0`. -/
noncomputable def alg3X {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    (inst : CoveringInstance I J) (y : J → ℝ) (i : I) : ℝ :=
  if dualSum inst y i < inst.c i then 0
  else min 1 ((1 / inst.d) * Real.exp (dualSum inst y i / inst.c i - 1))

end OnlinePrimalDual.Framework
