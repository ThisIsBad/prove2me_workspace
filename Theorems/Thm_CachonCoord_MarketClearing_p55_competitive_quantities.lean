import Mathlib
import Definitions.Def_CachonCoord_MarketClearing_Model

namespace CachonCoord.MarketClearing

/-- §6.5.2, p. 55: `q₁(w) ≤ 1` iff `w ≥ (1/2) − 1/(2θ)`, `q₂(w) > 1` iff `w < (1/2) − 1/(2θ)`, and for
a wholesale price `0 ≤ w < 1` the perfectly competitive total order is `q₁(w)` in the first case and
`q₂(w)` in the second (it exists and is unique). -/
theorem p55_competitive_quantities (θ w : ℝ) (hθ : 1 < θ) (hw0 : 0 ≤ w) (hw1 : w < 1) :
    (q1 θ w ≤ 1 ↔ wBar0 θ ≤ w) ∧
    (1 < q2 θ w ↔ w < wBar0 θ) ∧
    (wBar0 θ ≤ w → ∀ q : ℝ, IsCompetitiveOrder (retailerProfit θ w) q ↔ q = q1 θ w) ∧
    (w < wBar0 θ → ∀ q : ℝ, IsCompetitiveOrder (retailerProfit θ w) q ↔ q = q2 θ w) := by sorry

end CachonCoord.MarketClearing

