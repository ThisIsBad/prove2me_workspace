import Mathlib
import Definitions.Def_CachonPushPull_Coordination_Model

namespace CachonPushPull.Coordination

open MeasureTheory ProbabilityTheory

/-! ### The prebook game of §4.5 (p. 233) under a contract `{w₁, w₂}` (p. 226) -/

/-- Expected at-once sales when the retailer prebooks `y` and the supplier produces `q ≥ y`:
`S(q) - S(y)` when at-once orders are submitted (`w₂ ≤ p`), and `0` when `w₂ > p` (p. 226:
"with push `w₂ > p`, so at-once orders are never submitted"). -/
noncomputable def atOnceSales (μ : Measure ℝ) (p w₂ y q : ℝ) : ℝ :=
  if w₂ ≤ p then S μ q - S μ y else 0

/-- Supplier's expected profit (Eq. (20)):
`π_s(y, q) = (w₁ - v) y + (w₂ - v)(S(q) - S(y)) - (c - v) q`, with the at-once term switched off
when `w₂ > p`. -/
noncomputable def supplierProfit (μ : Measure ℝ) (p c v w₁ w₂ y q : ℝ) : ℝ :=
  (w₁ - v) * y + (w₂ - v) * atOnceSales μ p w₂ y q - (c - v) * q

/-- Retailer's expected profit (p. 233):
`π_r(y, q) = -(w₁ - v) y + (p - v) S(y) + (p - w₂)(S(q) - S(y))`, with the at-once term switched
off when `w₂ > p` (then it is the push profit `(p - v) S(y) - (w₁ - v) y`). -/
noncomputable def retailerProfit (μ : Measure ℝ) (p v w₁ w₂ y q : ℝ) : ℝ :=
  -(w₁ - v) * y + (p - v) * S μ y + (p - w₂) * atOnceSales μ p w₂ y q

/-- `q` is a best response of the supplier to the prebook `y`: `q ≥ y` and `q` maximizes the
supplier's profit over all production quantities `q' ≥ y`. -/
def IsSupplierBestResponse (μ : Measure ℝ) (p c v w₁ w₂ y q : ℝ) : Prop :=
  y ≤ q ∧ ∀ q' : ℝ, y ≤ q' → supplierProfit μ p c v w₁ w₂ y q' ≤ supplierProfit μ p c v w₁ w₂ y q

/-- An outcome `(y, q)` of the contract `{w₁, w₂}`: the prebook `y ≥ 0`, the production `q` is a
supplier best response to `y`, and no other prebook `y' ≥ 0`, followed by any supplier best
response `q'` to it, gives the retailer more than `(y, q)` does (the retailer anticipates the
supplier's response). -/
def IsOutcome (μ : Measure ℝ) (p c v w₁ w₂ y q : ℝ) : Prop :=
  0 ≤ y ∧ IsSupplierBestResponse μ p c v w₁ w₂ y q ∧
    ∀ y' q' : ℝ, 0 ≤ y' → IsSupplierBestResponse μ p c v w₁ w₂ y' q' →
      retailerProfit μ p v w₁ w₂ y' q' ≤ retailerProfit μ p v w₁ w₂ y q

/-- Push contract (p. 226): prebook price `c ≤ w₁ < p`, at-once price `w₂ > p`. -/
def IsPush (p c w₁ w₂ : ℝ) : Prop := c ≤ w₁ ∧ w₁ < p ∧ p < w₂

/-- Pull contract (p. 226): a single price `w₁ = w₂` with `c ≤ w₁ ≤ p` (the endpoint `w₁ = w₂ = p`
is included, following the remark in the proof of Theorem 7, p. 233). -/
def IsPull (p c w₁ w₂ : ℝ) : Prop := c ≤ w₁ ∧ w₁ = w₂ ∧ w₂ ≤ p

/-- Advance-purchase discount contract (p. 226): `c ≤ w₁ < w₂ ≤ p` (the boundary `w₂ = p` is
included, as Theorem 7 calls those contracts advance-purchase discounts). -/
def IsAPD (p c w₁ w₂ : ℝ) : Prop := c ≤ w₁ ∧ w₁ < w₂ ∧ w₂ ≤ p

/-- The contracts Theorem 7 compares: push, pull and advance-purchase discount contracts. -/
def IsAdmissible (p c w₁ w₂ : ℝ) : Prop := IsPush p c w₁ w₂ ∨ IsPull p c w₁ w₂ ∨ IsAPD p c w₁ w₂

/-- The payoff pair `(r', s')` Pareto dominates `(r, s)`: no firm is worse off and one firm is
strictly better off (p. 224). -/
def Dominates (r' s' r s : ℝ) : Prop :=
  r ≤ r' ∧ s ≤ s' ∧ (r < r' ∨ s < s')

/-- The contract `{w₁, w₂}` is Pareto among the push, pull and advance-purchase discount contracts:
it is one of them, and the payoff pair (retailer, supplier) of none of its outcomes is Pareto
dominated by the payoff pair of an outcome of any such contract. -/
def IsPareto (μ : Measure ℝ) (p c v w₁ w₂ : ℝ) : Prop :=
  IsAdmissible p c w₁ w₂ ∧
    ∀ y q : ℝ, IsOutcome μ p c v w₁ w₂ y q →
      ¬ ∃ w₁' w₂' y' q' : ℝ, IsAdmissible p c w₁' w₂' ∧ IsOutcome μ p c v w₁' w₂' y' q' ∧
        Dominates (retailerProfit μ p v w₁' w₂' y' q') (supplierProfit μ p c v w₁' w₂' y' q')
          (retailerProfit μ p v w₁ w₂ y q) (supplierProfit μ p c v w₁ w₂ y q)

end CachonPushPull.Coordination
