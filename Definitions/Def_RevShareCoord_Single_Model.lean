import Mathlib

namespace RevShareCoord.Single

/-- The single-retailer model of Sec. 1 (Cachon–Lariviere, June 2000 working paper, p. 5).
`R q` is the retailer's expected revenue from `q` units, `R'` its derivative on `q ≥ 0`
(one-sided at `0`), and `c` the supplier's unit production cost. -/
structure Model where
  /-- Expected revenue `R(q)` as a function of the order quantity. -/
  R : ℝ → ℝ
  /-- Marginal revenue `R'(q)` for `q ≥ 0`. -/
  R' : ℝ → ℝ
  /-- Supplier's unit production cost `c`. -/
  c : ℝ
  /-- `c > 0`. -/
  c_pos : 0 < c
  /-- `R` is strictly concave for `q ≥ 0`. -/
  strictConcave : StrictConcaveOn ℝ (Set.Ici 0) R
  /-- `R` is differentiable for `q ≥ 0`, with derivative `R'` (one-sided at `0`). -/
  hasDeriv : ∀ q : ℝ, 0 ≤ q → HasDerivWithinAt R (R' q) (Set.Ici 0) q
  /-- The product is viable: `R'(0) > c`. -/
  viable : c < R' 0
  /-- A finite quantity is optimal, `R'(∞) < c`: marginal revenue eventually falls below `c`. -/
  finite_optimal : ∃ Q : ℝ, 0 ≤ Q ∧ R' Q < c

namespace Model

variable (M : Model)

/-- Total supply chain profit `Π(q) = R(q) − qc` (Sec. 2.1, p. 6). -/
def Pi (q : ℝ) : ℝ := M.R q - q * M.c

/-- Retailer's profit under the revenue-sharing contract `{φ, w}`:
`π_r(q) = φR(q) − qw` (Sec. 2.2, p. 6). -/
def retailerProfit (φ w q : ℝ) : ℝ := φ * M.R q - q * w

/-- Supplier's profit under the revenue-sharing contract `{φ, w}`: she receives `wq` and
`(1 − φ)R(q)` and pays the production cost `qc` (Sec. 1, p. 5, sequence of events). -/
def supplierProfit (φ w q : ℝ) : ℝ := (1 - φ) * M.R q + q * w - q * M.c

end Model

end RevShareCoord.Single
