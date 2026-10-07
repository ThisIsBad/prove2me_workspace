import Mathlib
import Definitions.Def_CachonCoord_Proportional_Demand
import Definitions.Def_CachonCoord_Proportional_Nash

namespace CachonCoord.Proportional

open MeasureTheory

namespace Model

variable (M : Model)

/-- Retailer `i`'s expected profit `π_i(q_i, q_{−i})` under a buy-back contract with wholesale
price `w` and buy-back rate `b` (§6.5.1, pp. 48–50), when he stocks `x = q_i` and the other
retailers stock `s = q_{−i}` in total. Total demand `D` is allocated in proportion to stock,
`D_i = (q_i/q) D` with `q = q_i + q_{−i}` (p. 48); the retailer sells `min(q_i, D_i)` at `p`,
returns `(q_i − D_i)⁺` for `b` each, and pays `w` per unit ordered. With `b = 0` this is the
wholesale-price contract. (At `q = 0`, i.e. `x = s = 0`, Lean's `0/0 = 0` gives the profit `0`
of a retailer that orders nothing.) -/
noncomputable def retailerProfit (w b x s : ℝ) : ℝ :=
  ∫ d, (M.p * min x (x / (x + s) * d) + b * max (x - x / (x + s) * d) 0 - w * x) ∂M.law

/-- Total stock `q = ∑_i q_i` of a profile. -/
def total {n : ℕ} (q : Fin n → ℝ) : ℝ := ∑ i, q i

/-- Retailer `i`'s payoff at the profile `q`: `π_i(q_i, q − q_i)`. -/
noncomputable def payoff {n : ℕ} (w b : ℝ) (i : Fin n) (q : Fin n → ℝ) : ℝ :=
  M.retailerProfit w b (q i) (total q - q i)

/-- Nash equilibrium of the `n`-retailer ordering game under the contract `(w, b)` (p. 50):
every retailer's order `q_i ≥ 0` is a best response, over all orders `x ≥ 0`, to the others'. -/
def IsNashEq {n : ℕ} (w b : ℝ) (q : Fin n → ℝ) : Prop :=
  IsNash (M.payoff w b) q

/-- The left-hand side of (22), p. 51:
`L_n(q) = (1/n) F(q) + ((n − 1)/n) (1/q) ∫_0^q F(x) dx`. -/
noncomputable def lhs22 (n : ℕ) (q : ℝ) : ℝ :=
  (1 / (n : ℝ)) * M.F q + (((n : ℝ) - 1) / (n : ℝ)) * M.avgF q

/-- The wholesale price `ŵ(q)` printed on p. 52:
`ŵ(q) = p (1 − (1/n) F(q) − ((n − 1)/n) (1/q) ∫_0^q F(x) dx)`. -/
noncomputable def what (n : ℕ) (q : ℝ) : ℝ :=
  M.p * (1 - (1 / (n : ℝ)) * M.F q - (((n : ℝ) - 1) / (n : ℝ)) * M.avgF q)

/-- The buy-back wholesale price `w_b(b)` printed at the foot of p. 52, at the integrated
optimum `qo` (the book's `q°`):
`w_b(b) = p − (p − b) [(1/n)((p − c)/p) + ((n − 1)/n) (1/q°) ∫_0^{q°} F(x) dx]`. -/
noncomputable def wb (n : ℕ) (b qo : ℝ) : ℝ :=
  M.p - (M.p - b) * ((1 / (n : ℝ)) * ((M.p - M.c) / M.p) +
    (((n : ℝ) - 1) / (n : ℝ)) * M.avgF qo)

/-- The supplier's expected profit when the retailers stock `q` units in total under the
contract `(w, b)`: wholesale revenue `wq`, minus production cost `cq`, minus the buy-back
payment `b` on every unit left over, `b E[(q − D)⁺]` (pp. 50–53). -/
noncomputable def supplierProfit (w b q : ℝ) : ℝ :=
  w * q - M.c * q - b * M.I q

end Model

end CachonCoord.Proportional
