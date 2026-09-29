import Mathlib
import Definitions.Def_ZhengQR_EOQHeuristic_qrCost

namespace ZhengQR.EOQHeuristic

/-- Eq. (6), p. 91: `H(Q) = G(r(Q))` for `Q > 0`, and `H(0) = G(y⁰)` (the value the paper assigns
at `0`). The value for `Q < 0` is a placeholder and is never used. -/
noncomputable def hFun (G : ℝ → ℝ) (lam K Q : ℝ) : ℝ :=
  if 0 < Q then G (reorderPt G lam K Q) else G (minPt G)

/-- `H₀(Q) = H(Q) − G(y⁰)`, p. 92. -/
noncomputable def h0Fun (G : ℝ → ℝ) (lam K Q : ℝ) : ℝ :=
  hFun G lam K Q - G (minPt G)

/-- `C(Q) = c(Q, r(Q))`, p. 91: the average cost when the reorder point is chosen optimally for
the order quantity `Q`. Meaningful for `Q > 0` only. -/
noncomputable def optCost (G : ℝ → ℝ) (lam K Q : ℝ) : ℝ :=
  qrCost G lam K Q (reorderPt G lam K Q)

/-- Eq. (9), p. 92: `A(Q) = Q H(Q) − ∫_0^Q H(y) dy`. -/
noncomputable def aFun (G : ℝ → ℝ) (lam K Q : ℝ) : ℝ :=
  Q * hFun G lam K Q - ∫ y in (0 : ℝ)..Q, hFun G lam K y

/-- `Q` is an optimal order quantity (p. 92, `Q*`): `Q > 0` and `C(Q) ≤ C(Q')` for every `Q' > 0`. -/
def IsOptQty (G : ℝ → ℝ) (lam K Q : ℝ) : Prop :=
  0 < Q ∧ ∀ Q' : ℝ, 0 < Q' → optCost G lam K Q ≤ optCost G lam K Q'

end ZhengQR.EOQHeuristic
