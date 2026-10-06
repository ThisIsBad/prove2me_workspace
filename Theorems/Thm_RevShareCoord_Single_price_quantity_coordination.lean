import Mathlib
import Definitions.Def_RevShareCoord_Single_PriceQuantity

namespace RevShareCoord.Single

/-- Sec. 3.1 and footnote 3, p. 11: let revenue `Rev(q, p)` be any function of quantity and
price, costs linear in quantity at unit cost `c`, and let `(q_I, p_I)` be the integrated channel's
unique optimal quantity–price pair over `q ≥ 0` and admissible prices `p ∈ P`. Under the
revenue-sharing contract `{φ, φc}` with `φ ∈ (0, 1]`, the retailer's profit is `φ` times the
integrated profit at every `(q, p)`, and `(q_I, p_I)` is the retailer's unique optimum. -/
theorem price_quantity_coordination (Rev : ℝ → ℝ → ℝ) (c φ : ℝ) (hc : 0 < c)
    (hφ0 : 0 < φ) (hφ1 : φ ≤ 1) (P : Set ℝ) (qI pI : ℝ) (hqI : 0 ≤ qI) (hpI : pI ∈ P)
    (hopt : IsMaxOn (fun x : ℝ × ℝ => pqChainProfit Rev c x.1 x.2) (Set.Ici 0 ×ˢ P) (qI, pI))
    (huniq : ∀ x ∈ Set.Ici (0 : ℝ) ×ˢ P,
      IsMaxOn (fun x : ℝ × ℝ => pqChainProfit Rev c x.1 x.2) (Set.Ici 0 ×ˢ P) x → x = (qI, pI)) :
    (∀ q p : ℝ, pqRetailerProfit Rev φ (φ * c) q p = φ * pqChainProfit Rev c q p) ∧
    IsMaxOn (fun x : ℝ × ℝ => pqRetailerProfit Rev φ (φ * c) x.1 x.2) (Set.Ici 0 ×ˢ P) (qI, pI) ∧
    ∀ x ∈ Set.Ici (0 : ℝ) ×ˢ P,
      IsMaxOn (fun x : ℝ × ℝ => pqRetailerProfit Rev φ (φ * c) x.1 x.2) (Set.Ici 0 ×ˢ P) x →
        x = (qI, pI) := by sorry

end RevShareCoord.Single

