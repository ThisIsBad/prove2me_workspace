import Mathlib

namespace BinPacking.FirstFit

/-- The weighting function `W : [0, 1] → [0, 1]` of the proof of Theorem 2.2 (p. 304, Fig. 2):
`W(α) = (6/5)α` for `0 ≤ α ≤ 1/6`, `(9/5)α − 1/10` for `1/6 < α ≤ 1/3`,
`(6/5)α + 1/10` for `1/3 < α ≤ 1/2`, and `1` for `1/2 < α ≤ 1`.
As a function `ℝ → ℝ` its values outside `[0, 1]` are not the paper's (`(6/5)α` below `0`,
`1` above `1`); every statement restricts its arguments to `(0, 1]`. -/
noncomputable def W (α : ℝ) : ℝ :=
  if α ≤ 1 / 6 then 6 / 5 * α
  else if α ≤ 1 / 3 then 9 / 5 * α - 1 / 10
  else if α ≤ 1 / 2 then 6 / 5 * α + 1 / 10
  else 1

end BinPacking.FirstFit
