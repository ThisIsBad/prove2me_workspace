import Mathlib

namespace ZhengQR.CostBounds

open MeasureTheory Classical

/-- Eq. (1), p. 88: the average cost of the `(Q, r)` policy for a generic inventory-cost rate `G`,
`c(Q, r) = (λK + ∫_r^{r+Q} G(y) dy) / Q`. Meaningful for `Q > 0` only. -/
noncomputable def qrCost (G : ℝ → ℝ) (lam K Q r : ℝ) : ℝ :=
  (lam * K + ∫ y in r..r + Q, G y) / Q

/-- p. 90: `r` is an optimal reorder point for the fixed order quantity `Q`, i.e. `r` minimizes
`c(Q, ·)` over all of `ℝ`. -/
def IsOptReorder (G : ℝ → ℝ) (lam K Q r : ℝ) : Prop :=
  ∀ r' : ℝ, qrCost G lam K Q r ≤ qrCost G lam K Q r'

/-- p. 90: `r(Q)`, a chosen optimal reorder point for `Q` (junk value `0` if none exists). -/
noncomputable def reorderPt (G : ℝ → ℝ) (lam K Q : ℝ) : ℝ :=
  if hr : ∃ r, IsOptReorder G lam K Q r then hr.choose else 0

/-- p. 90: `y⁰`, a chosen global minimizer of `G` (the unique one under the paper's standing
assumption; junk value `0` if `G` has no minimizer). -/
noncomputable def idealPt (G : ℝ → ℝ) : ℝ :=
  if hy : ∃ y, ∀ z, G y ≤ G z then hy.choose else 0

/-- Eq. (6) and the line under it, p. 91: `H(Q) = G(r(Q))` for `Q > 0`, and `H(0) = G(y⁰)`.
(For `Q < 0` the value `G(y⁰)` is a junk value; the paper uses `H` on `[0, ∞)` only.) -/
noncomputable def Hfun (G : ℝ → ℝ) (lam K Q : ℝ) : ℝ :=
  if 0 < Q then G (reorderPt G lam K Q) else G (idealPt G)

/-- p. 91: `C(Q) = c(Q, r(Q))`, the average cost when the reorder point is optimal for `Q`. -/
noncomputable def Cfun (G : ℝ → ℝ) (lam K Q : ℝ) : ℝ :=
  qrCost G lam K Q (reorderPt G lam K Q)

/-- Eq. (9), p. 92: `A(Q) = Q H(Q) − ∫_0^Q H(y) dy`. -/
noncomputable def Afun (G : ℝ → ℝ) (lam K Q : ℝ) : ℝ :=
  Q * Hfun G lam K Q - ∫ y in (0 : ℝ)..Q, Hfun G lam K y

/-- p. 92: `H₀(Q) = H(Q) − G(y⁰)`. -/
noncomputable def H0fun (G : ℝ → ℝ) (lam K Q : ℝ) : ℝ :=
  Hfun G lam K Q - G (idealPt G)

/-- Eq. (14), p. 92: the average controllable cost `C₀(Q) = (λK + ∫_0^Q H₀(y) dy) / Q`. -/
noncomputable def C0fun (G : ℝ → ℝ) (lam K Q : ℝ) : ℝ :=
  (lam * K + ∫ y in (0 : ℝ)..Q, H0fun G lam K y) / Q

/-- p. 92: `Q` is an optimal order quantity: `Q > 0` and `C(Q) ≤ C(Q')` for every `Q' > 0`. -/
def IsOptQty (G : ℝ → ℝ) (lam K Q : ℝ) : Prop :=
  0 < Q ∧ ∀ Q' : ℝ, 0 < Q' → Cfun G lam K Q ≤ Cfun G lam K Q'

end ZhengQR.CostBounds
