import Mathlib

namespace ZhengQR.Flatness

/-- Zheng (1992), p. 88, Eq. (1): the long-run average cost of the `(Q, r)` policy,
`c(Q, r) = (λK + ∫_r^{r+Q} G(y) dy) / Q`, for an inventory cost rate `G`, demand rate `lam`
and fixed ordering cost `K`. Meaningful for `Q > 0` only. -/
noncomputable def qrCost (G : ℝ → ℝ) (lam K Q r : ℝ) : ℝ :=
  (lam * K + ∫ y in r..r + Q, G y) / Q

/-- `r` is an optimal reorder point for the fixed order quantity `Q`: it minimizes
`c(Q, ·)` over all of `ℝ` (Zheng 1992, p. 90). -/
def IsOptReorder (G : ℝ → ℝ) (lam K Q r : ℝ) : Prop :=
  ∀ r' : ℝ, qrCost G lam K Q r ≤ qrCost G lam K Q r'

open Classical in
/-- Zheng (1992), p. 90: `r(Q)`, an optimal reorder point for `Q` fixed, chosen among the
minimizers of `c(Q, ·)` (junk value `0` if there is none). -/
noncomputable def optReorder (G : ℝ → ℝ) (lam K Q : ℝ) : ℝ :=
  if hex : ∃ r, IsOptReorder G lam K Q r then hex.choose else 0

open Classical in
/-- `y⁰`: a global minimizer of `G` (Zheng 1992, p. 90), chosen; junk value `0` if `G`
has no global minimizer. -/
noncomputable def minPoint (G : ℝ → ℝ) : ℝ :=
  if hex : ∃ y, ∀ z, G y ≤ G z then hex.choose else 0

/-- Zheng (1992), p. 91, Eq. (6): `H(Q) = G(r(Q))` for `Q > 0`, and `H(0) = G(y⁰)`.
(For `Q < 0` the value `G(y⁰)` is a junk value; the paper uses `H` on `[0, ∞)` only.) -/
noncomputable def Hfun (G : ℝ → ℝ) (lam K Q : ℝ) : ℝ :=
  if 0 < Q then G (optReorder G lam K Q) else G (minPoint G)

/-- Zheng (1992), p. 92: `H₀(Q) = H(Q) - G(y⁰)`. -/
noncomputable def Hzero (G : ℝ → ℝ) (lam K Q : ℝ) : ℝ :=
  Hfun G lam K Q - G (minPoint G)

/-- Zheng (1992), p. 91: `C(Q) = c(Q, r(Q))`, the average cost of order quantity `Q` when the
reorder point is chosen optimally for `Q`. Meaningful for `Q > 0` only. -/
noncomputable def optCost (G : ℝ → ℝ) (lam K Q : ℝ) : ℝ :=
  qrCost G lam K Q (optReorder G lam K Q)

/-- Zheng (1992), p. 92, Eq. (9): `A(Q) = Q H(Q) - ∫_0^Q H(y) dy`. -/
noncomputable def Afun (G : ℝ → ℝ) (lam K Q : ℝ) : ℝ :=
  Q * Hfun G lam K Q - ∫ y in (0 : ℝ)..Q, Hfun G lam K y

end ZhengQR.Flatness
