import Mathlib

namespace CachonCoord.MarketClearing

/-- Low-demand market clearing price `p_l(q) = (1 − q)⁺` for the retailers' total stock `q`
(Cachon 2003, 3rd draft, §6.5.2, p. 53). -/
noncomputable def pl (q : ℝ) : ℝ := max (1 - q) 0

/-- High-demand market clearing price `p_h(q) = (1 − q/θ)⁺`, `θ > 1`
(Cachon 2003, 3rd draft, §6.5.2, p. 54). -/
noncomputable def ph (θ q : ℝ) : ℝ := max (1 - q / θ) 0

/-- The perfectly competitive retailers' expected profit under a wholesale price `w`, as a
function of their total order `q`: both states equally likely, all stock sold at the market
clearing price, no salvage value: `(1/2)p_l(q)q + (1/2)p_h(q)q − wq` (§6.5.2, p. 54). -/
noncomputable def retailerProfit (θ w q : ℝ) : ℝ :=
  (1 / 2) * pl q * q + (1 / 2) * ph θ q * q - w * q

/-- Perfect competition (§6.5.2, p. 54: "the retailers continue to order inventory until their
expected profit is zero"): the total order `q > 0` is a competitive outcome of the aggregate
expected-profit function `π` if `π(q) = 0` while `π(x) > 0` for every smaller positive order `x`. -/
def IsCompetitiveOrder (π : ℝ → ℝ) (q : ℝ) : Prop :=
  0 < q ∧ π q = 0 ∧ ∀ x : ℝ, 0 < x → x < q → 0 < π x

/-- The supplier's attainable profits with a wholesale price contract (production cost zero):
the values `w·q` over all wholesale prices `w` and competitive total orders `q` at `w`. -/
def wholesaleOutcomes (θ : ℝ) : Set ℝ :=
  {v | ∃ w q : ℝ, IsCompetitiveOrder (retailerProfit θ w) q ∧ v = w * q}

/-- The monopolist's attainable expected profits (§6.5.2, p. 54): she orders a stock `Q`
(production cost zero) and, after observing the state, sells `x_l ∈ [0, Q]` units in the low state
and `x_h ∈ [0, Q]` in the high state at the market clearing prices; unsold units are worthless. -/
def monopolyOutcomes (θ : ℝ) : Set ℝ :=
  {v | ∃ Q xl xh : ℝ, 0 ≤ xl ∧ xl ≤ Q ∧ 0 ≤ xh ∧ xh ≤ Q ∧
    v = (1 / 2) * pl xl * xl + (1 / 2) * ph θ xh * xh}

/-- `q₁(w) = (2θ/(1 + θ))(1 − w)` (§6.5.2, p. 55). -/
noncomputable def q1 (θ w : ℝ) : ℝ := (2 * θ / (1 + θ)) * (1 - w)

/-- `q₂(w) = θ(1 − 2w)` (§6.5.2, p. 55). -/
noncomputable def q2 (θ w : ℝ) : ℝ := θ * (1 - 2 * w)

/-- The branch threshold `(1/2) − 1/(2θ)` of p. 55. -/
noncomputable def wBar0 (θ : ℝ) : ℝ := 1 / 2 - 1 / (2 * θ)

/-- The supplier's profit `π_s(w)` as displayed on p. 55: `q₁(w)w` if `w ≥ (1/2) − 1/(2θ)`,
`q₂(w)w` otherwise. -/
noncomputable def supplierProfit (θ w : ℝ) : ℝ :=
  if wBar0 θ ≤ w then q1 θ w * w else q2 θ w * w

/-- The page's `w*(θ)`: `1/2` if `θ ≤ 3`, `1/4` otherwise (p. 55). -/
noncomputable def wStar (θ : ℝ) : ℝ := if θ ≤ 3 then 1 / 2 else 1 / 4

end CachonCoord.MarketClearing
