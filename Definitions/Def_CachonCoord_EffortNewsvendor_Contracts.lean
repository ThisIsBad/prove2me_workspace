import Mathlib
import Definitions.Def_CachonCoord_EffortNewsvendor_Model

namespace CachonCoord.EffortNewsvendor

namespace Model

variable (M : Model)

/-- Retailer's profit with a buy back contract `{w_b, b}` (p. 42):
`π_r(q, e, w_b, b) = (p − b)S(q, e) − (w_b − b)q − g(e)`. -/
noncomputable def bbRetailerProfit (wb b q e : ℝ) : ℝ :=
  (M.p - b) * M.S q e - (wb - b) * q - M.effortCost e

/-- Retailer's profit with a quantity-flexibility contract `{w_q, δ}` (p. 42):
`π_r(q, e, w_q, δ) = pS(q, e) − w_q (q − ∫_{(1−δ)q}^q F(y|e) dy) − g(e)`. -/
noncomputable def qfRetailerProfit (wq δ q e : ℝ) : ℝ :=
  M.p * M.S q e - wq * (q - ∫ y in (1 - δ) * q..q, M.F y e) - M.effortCost e

/-- Retailer's profit with a revenue sharing contract `{w_r, φ}`: §6.2.4's
`π_r = (φ(p − v) + g_r)S(q) − (w_r + c_r − φv)q − g_r μ` (p. 21) with `v = g_r = c_r = 0`,
less the effort cost: `φ p S(q, e) − w_r q − g(e)`. -/
noncomputable def rsRetailerProfit (wr φ q e : ℝ) : ℝ :=
  φ * M.p * M.S q e - wr * q - M.effortCost e

/-- The sales rebate transfer `T_s(q, w_s, r, t)` of §6.2.6 (p. 27), with demand distribution
`F(·|e)`: `w_s q` if `q < t`, and `(w_s − r)q + r(t + ∫_t^q F(y|e) dy)` if `q ≥ t`. -/
noncomputable def srTransfer (ws r t q e : ℝ) : ℝ :=
  if q < t then ws * q else (ws - r) * q + r * (t + ∫ y in t..q, M.F y e)

/-- Retailer's profit with a sales rebate contract `{w_s, r, t}`: §6.2.6's
`π_r = (p − v + g_r)S(q) − (c_r − v)q − g_r μ − T_s` (p. 27) with `v = g_r = c_r = 0`,
less the effort cost: `pS(q, e) − T_s(q, w_s, r, t) − g(e)`. -/
noncomputable def srRetailerProfit (ws r t q e : ℝ) : ℝ :=
  M.p * M.S q e - M.srTransfer ws r t q e - M.effortCost e

/-- The quantity discount schedule of p. 43, for `q > 0`, built on the optimal effort `e°`
(argument `eo`) and a share `λ` (argument `lam`):
`w_d(q) = (1 − λ)p (S(q, e°)/q) + λc − (1 − λ) g(e°)/q`.
The sign of the last term is the one under which the page's displayed `π_r(q, e)` and
`π_r(q, e°) = λΠ(q, e°)` hold; the page prints `+ (1 − λ) g(e°)/q`. -/
noncomputable def qdWholesale (lam eo q : ℝ) : ℝ :=
  (1 - lam) * M.p * (M.S q eo / q) + lam * M.c - (1 - lam) * M.effortCost eo / q

/-- Retailer's profit with the quantity discount, transfer `T_d(q) = w_d(q) q`:
`π_r(q, e) = pS(q, e) − w_d(q) q − g(e)`. -/
noncomputable def qdRetailerProfit (lam eo q e : ℝ) : ℝ :=
  M.p * M.S q e - M.qdWholesale lam eo q * q - M.effortCost e

/-- Supplier's profit with the quantity discount: `π_s(q) = w_d(q) q − cq`. -/
noncomputable def qdSupplierProfit (lam eo q : ℝ) : ℝ :=
  M.qdWholesale lam eo q * q - M.c * q

end Model

end CachonCoord.EffortNewsvendor
