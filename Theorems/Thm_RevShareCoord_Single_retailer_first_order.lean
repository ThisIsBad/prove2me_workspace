import Mathlib
import Definitions.Def_RevShareCoord_Single_Model

namespace RevShareCoord.Single

/-- Sec. 2.2, p. 6: under a revenue-sharing contract `{φ, w}` with `φ ∈ (0, 1]`, `w ≥ 0` and
`R'(0) > w/φ`, an order quantity `q̂ ≥ 0` is optimal for the retailer exactly when `q̂ > 0` and
`φR'(q̂) = w`; and the retailer has at most one optimal order quantity. -/
theorem retailer_first_order (M : Model) (φ w : ℝ) (hφ0 : 0 < φ) (hφ1 : φ ≤ 1) (hw : 0 ≤ w)
    (hR0 : w / φ < M.R' 0) :
    (∀ qhat : ℝ, 0 ≤ qhat →
      (IsMaxOn (M.retailerProfit φ w) (Set.Ici 0) qhat ↔ 0 < qhat ∧ φ * M.R' qhat = w)) ∧
    (∀ q₁ q₂ : ℝ, 0 ≤ q₁ → 0 ≤ q₂ →
      IsMaxOn (M.retailerProfit φ w) (Set.Ici 0) q₁ →
      IsMaxOn (M.retailerProfit φ w) (Set.Ici 0) q₂ → q₁ = q₂) := by sorry

end RevShareCoord.Single

