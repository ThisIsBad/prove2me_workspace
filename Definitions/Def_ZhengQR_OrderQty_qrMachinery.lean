import Mathlib

namespace ZhengQR.OrderQty

/-- Eq. (1), p. 88: the long-run average cost of the `(Q, r)` policy with order quantity `Q` and
reorder point `r`, for an inventory cost rate `G`, demand rate `λ` and fixed ordering cost `K`:
`c(Q, r) = (λK + ∫_r^{r+Q} G(y) dy) / Q`. Meaningful for `Q > 0` only. -/
noncomputable def qrCost (G : ℝ → ℝ) (lam K Q r : ℝ) : ℝ :=
  (lam * K + ∫ y in r..r + Q, G y) / Q

/-- `r` is an optimal reorder point for the fixed order quantity `Q` (p. 90): it minimizes
`c(Q, ·)` over all of `ℝ`. -/
def IsOptReorder (G : ℝ → ℝ) (lam K Q r : ℝ) : Prop :=
  ∀ r' : ℝ, qrCost G lam K Q r ≤ qrCost G lam K Q r'

open Classical in
/-- `r(Q)`, "an optimal `r` for `Q` fixed" (p. 90): a chosen minimizer of the inventory-cost
integral `r ↦ ∫_r^{r+Q} G(y) dy` (junk value `0` if there is none). For `Q > 0` these are exactly
the minimizers of `c(Q, ·)`, since `c(Q, r) = (λK + ∫_r^{r+Q} G)/Q` with `λK/Q` a constant; the
choice therefore does not involve `λ` or `K` (cf. Lemma 3, part 1). -/
noncomputable def optReorder (G : ℝ → ℝ) (Q : ℝ) : ℝ :=
  if h : ∃ r, ∀ r' : ℝ, (∫ y in r..r + Q, G y) ≤ ∫ y in r'..r' + Q, G y then h.choose else 0

/-- `y` is a global minimizer of `G`. -/
def IsMinimizer (G : ℝ → ℝ) (y : ℝ) : Prop :=
  ∀ z : ℝ, G y ≤ G z

open Classical in
/-- `y⁰` (p. 90): a chosen global minimizer of `G` (the unique one under the paper's standing
assumption; junk value `0` if there is none). -/
noncomputable def minPoint (G : ℝ → ℝ) : ℝ :=
  if h : ∃ y, IsMinimizer G y then h.choose else 0

/-- Eq. (6), p. 91: `H(Q) = G(r(Q))` for `Q > 0`, and `H(0) = G(y⁰)`. (For `Q < 0` the value
`G(y⁰)` is a junk value; every statement uses `H` on `[0, ∞)` only.) -/
noncomputable def Hfun (G : ℝ → ℝ) (Q : ℝ) : ℝ :=
  if 0 < Q then G (optReorder G Q) else G (minPoint G)

/-- p. 91: the cost of order quantity `Q` with the reorder point chosen optimally,
`C(Q) = c(Q, r(Q))`. -/
noncomputable def optCost (G : ℝ → ℝ) (lam K Q : ℝ) : ℝ :=
  qrCost G lam K Q (optReorder G Q)

/-- Eq. (9), p. 92: `A(Q) = Q H(Q) - ∫_0^Q H(y) dy`. -/
noncomputable def Afun (G : ℝ → ℝ) (Q : ℝ) : ℝ :=
  Q * Hfun G Q - ∫ y in (0 : ℝ)..Q, Hfun G y

/-- p. 92: `H₀(Q) = H(Q) - G(y⁰)`. -/
noncomputable def H0fun (G : ℝ → ℝ) (Q : ℝ) : ℝ :=
  Hfun G Q - G (minPoint G)

/-- `Q` is an optimal order quantity (p. 92): `Q > 0` and `C(Q) ≤ C(Q')` for every `Q' > 0`. -/
def IsOptQty (G : ℝ → ℝ) (lam K Q : ℝ) : Prop :=
  0 < Q ∧ ∀ Q' : ℝ, 0 < Q' → optCost G lam K Q ≤ optCost G lam K Q'

end ZhengQR.OrderQty
