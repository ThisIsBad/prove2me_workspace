import Mathlib
import Definitions.Def_CachonPushPull_ShippingCost_Model

namespace CachonPushPull.ShippingCost

open MeasureTheory ProbabilityTheory

/-! ### The prebook game of §4.5 (p. 233) with the at-once shipping cost `τ` of §5.1 (p. 234)

A contract is a pair of wholesale prices `{w₁, w₂}` (p. 226): the retailer prebooks `y ≥ 0` units
at `w₁` before production, the supplier produces `q ≥ y`, and during the season the retailer's
at-once orders are filled at `w₂` from the supplier's remaining stock. The formulas below are
those of §4.5 for contracts with `w₂ ≤ p` (at-once orders are submitted); every theorem of this
mission assumes `w₂ ≤ p`. -/

/-- Retailer's expected profit (p. 233), unchanged by the shipping cost:
`π_r(y, q) = -(w₁ - v) y + (p - v) S(y) + (p - w₂)(S(q) - S(y))`. -/
noncomputable def retailerProfit (μ : Measure ℝ) (p v w₁ w₂ y q : ℝ) : ℝ :=
  -(w₁ - v) * y + (p - v) * S μ y + (p - w₂) * (S μ q - S μ y)

/-- Supplier's expected profit with the at-once shipping and handling cost `τ` per unit (§5.1,
p. 234): Eq. (20) with the at-once wholesale price `w₂` replaced by her net revenue `w₂ - τ`,
`π_s(y, q) = (w₁ - v) y + (w₂ - τ - v)(S(q) - S(y)) - (c - v) q`. -/
noncomputable def supplierProfit (μ : Measure ℝ) (c v τ w₁ w₂ y q : ℝ) : ℝ :=
  (w₁ - v) * y + (w₂ - τ - v) * (S μ q - S μ y) - (c - v) * q

/-- `q` is a best response of the supplier to the prebook `y`: `q ≥ y` and `q` maximizes the
supplier's profit over all production quantities `q' ≥ y`. -/
def IsSupplierBestResponse (μ : Measure ℝ) (c v τ w₁ w₂ y q : ℝ) : Prop :=
  y ≤ q ∧ ∀ q' : ℝ, y ≤ q' → supplierProfit μ c v τ w₁ w₂ y q' ≤ supplierProfit μ c v τ w₁ w₂ y q

/-- An outcome `(y, q)` of the contract `{w₁, w₂}`: the prebook `y ≥ 0`, the production `q` is a
supplier best response to `y`, and no other prebook `y' ≥ 0`, followed by any supplier best
response `q'` to it, gives the retailer more than `(y, q)` does (the retailer anticipates the
supplier's response). -/
def IsOutcome (μ : Measure ℝ) (p c v τ w₁ w₂ y q : ℝ) : Prop :=
  0 ≤ y ∧ IsSupplierBestResponse μ c v τ w₁ w₂ y q ∧
    ∀ y' q' : ℝ, 0 ≤ y' → IsSupplierBestResponse μ c v τ w₁ w₂ y' q' →
      retailerProfit μ p v w₁ w₂ y' q' ≤ retailerProfit μ p v w₁ w₂ y q

/-- "The retailer does not prebook when there is no advance-purchase discount" (Theorem 8,
p. 234), for the pull contract `w₁ = w₂`: the supplier has a best response `q₀` to the prebook
`0`, and every positive prebook `y > 0`, followed by any supplier best response `q` to it, gives
the retailer strictly less than prebooking nothing. Equivalently, `y = 0` is the retailer's
unique best reply under `{w₂, w₂}`. -/
def PullNoPrebook (μ : Measure ℝ) (p c v τ w₂ : ℝ) : Prop :=
  ∃ q₀ : ℝ, IsSupplierBestResponse μ c v τ w₂ w₂ 0 q₀ ∧
    ∀ y q : ℝ, 0 < y → IsSupplierBestResponse μ c v τ w₂ w₂ y q →
      retailerProfit μ p v w₂ w₂ y q < retailerProfit μ p v w₂ w₂ 0 q₀

end CachonPushPull.ShippingCost
