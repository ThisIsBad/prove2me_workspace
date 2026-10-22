import Mathlib

namespace RevShareCoord.Effort

/-! The linear-demand example of Sec. 4.2.2 (Cachon–Lariviere, June 2000 working paper,
pp. 23–24): inverse demand `P(q, e) = 1 − q + 2τe`, revenue `R(q, e) = qP(q, e)`, effort cost
`g(e) = e²`. Quantities and efforts range over `[0, ∞)`. -/

namespace Linear

/-- The retailer's decision set `{(q, e) : q ≥ 0, e ≥ 0}`. -/
def quadrant : Set (ℝ × ℝ) := Set.Ici 0 ×ˢ Set.Ici 0

/-- Inverse demand `P(q, e) = 1 − q + 2τe`. -/
def price (τ q e : ℝ) : ℝ := 1 - q + 2 * τ * e

/-- Expected revenue `R(q, e) = qP(q, e)`. -/
def revenue (τ q e : ℝ) : ℝ := q * price τ q e

/-- The retailer's profit `π_r(q, e) = φR(q, e) − e² − qw`. -/
def retailerProfit (τ φ w q e : ℝ) : ℝ := φ * revenue τ q e - e ^ 2 - q * w

/-- The supplier's profit `(1 − φ)R(q, e) + q(w − c)` when the retailer chooses `(q, e)`. -/
def supplierProfit (τ c φ w q e : ℝ) : ℝ := (1 - φ) * revenue τ q e + q * (w - c)

/-- The integrated channel's profit `Π(q, e) = R(q, e) − e² − qc`. -/
def channelProfit (τ c q e : ℝ) : ℝ := revenue τ q e - e ^ 2 - q * c

/-- `x = (q, e)` is an optimal response of the retailer to the contract `{φ, w}`: it maximizes
`π_r` over all `q ≥ 0`, `e ≥ 0`, jointly. -/
def IsRetailerResponse (τ φ w : ℝ) (x : ℝ × ℝ) : Prop :=
  x ∈ quadrant ∧ IsMaxOn (fun y : ℝ × ℝ => retailerProfit τ φ w y.1 y.2) quadrant x

/-- The page's effort rule `e(q) = φτq`. -/
def effort (τ φ q : ℝ) : ℝ := φ * τ * q

/-- The page's order rule `q(w, φ) = (φ − w)/(2(φ − φ²τ²))` if `w < φ`, otherwise `0`. -/
noncomputable def orderQty (τ φ w : ℝ) : ℝ :=
  if w < φ then (φ - w) / (2 * (φ - φ ^ 2 * τ ^ 2)) else 0

/-- The supplier's profit `π_s(w, φ) = (1 − φ)R(q(w, φ), e(q(w, φ))) + q(w, φ)(w − c)`. -/
noncomputable def supplierProfitAt (τ c φ w : ℝ) : ℝ :=
  supplierProfit τ c φ w (orderQty τ φ w) (effort τ φ (orderQty τ φ w))

/-- The page's wholesale price `w(φ) = φ((1 − τ²)φ + c(1 − φτ²))/(1 + φ(1 − 2τ²))`. -/
noncomputable def wholesalePrice (τ c φ : ℝ) : ℝ :=
  φ * ((1 - τ ^ 2) * φ + c * (1 - φ * τ ^ 2)) / (1 + φ * (1 - 2 * τ ^ 2))

/-- The retail price of the integrated channel, `P` at the retailer's solution with `w = c`,
`φ = 1`. -/
noncomputable def integratedPrice (τ c : ℝ) : ℝ :=
  price τ (orderQty τ 1 c) (effort τ 1 (orderQty τ 1 c))

/-- The supplier's profits attainable with the share `φ`: the profit `(1 − φ)R(q, e) + q(w − c)`
for some wholesale price `w ≥ 0` and some optimal response `(q, e)` of the retailer to `{φ, w}`. -/
def supplierOutcomes (τ c φ : ℝ) : Set ℝ :=
  {s | ∃ w : ℝ, 0 ≤ w ∧ ∃ x : ℝ × ℝ, IsRetailerResponse τ φ w x ∧
    s = supplierProfit τ c φ w x.1 x.2}

/-- The supplier's optimal profit with the share `φ`, `V(φ) = sup_{w ≥ 0} π_s(w, φ)`. -/
noncomputable def supplierValue (τ c φ : ℝ) : ℝ := sSup (supplierOutcomes τ c φ)

end Linear

end RevShareCoord.Effort
