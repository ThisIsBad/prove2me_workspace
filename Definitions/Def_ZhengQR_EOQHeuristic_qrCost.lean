import Mathlib

namespace ZhengQR.EOQHeuristic

/-- Eq. (1) of Zheng (1992), p. 88: the long-run average cost of the `(Q, r)` policy with order
quantity `Q` and reorder point `r`, for an inventory-cost rate `G`, demand rate `lam` and fixed
ordering cost `K`: `c(Q, r) = (λK + ∫_r^{r+Q} G(y) dy) / Q`. Meaningful for `Q > 0` only. -/
noncomputable def qrCost (G : ℝ → ℝ) (lam K Q r : ℝ) : ℝ :=
  (lam * K + ∫ y in r..r + Q, G y) / Q

/-- `r` is an optimal reorder point for the fixed order quantity `Q` (p. 90: "an optimal `r` for
`Q` fixed"): it minimizes `c(Q, ·)` over all of `ℝ`. -/
def IsOptReorder (G : ℝ → ℝ) (lam K Q r : ℝ) : Prop :=
  ∀ r' : ℝ, qrCost G lam K Q r ≤ qrCost G lam K Q r'

open Classical in
/-- `r(Q)` (p. 90): a chosen minimizer of `c(Q, ·)`; `0` if no minimizer exists. -/
noncomputable def reorderPt (G : ℝ → ℝ) (lam K Q : ℝ) : ℝ :=
  if hr : ∃ r, IsOptReorder G lam K Q r then hr.choose else 0

open Classical in
/-- `y⁰` (p. 90): a chosen global minimizer of `G`; `0` if `G` has no minimizer. -/
noncomputable def minPt (G : ℝ → ℝ) : ℝ :=
  if hy : ∃ y, ∀ z, G y ≤ G z then hy.choose else 0

end ZhengQR.EOQHeuristic
