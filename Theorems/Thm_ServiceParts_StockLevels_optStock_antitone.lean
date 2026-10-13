import Mathlib
import Definitions.Def_ServiceParts_StockLevels_CompoundPoissonDemand
import Definitions.Def_ServiceParts_StockLevels_Problems

namespace ServiceParts.StockLevels

theorem optStock_antitone {ι : Type*} [Fintype ι] (d : ι → CompoundPoissonDemand)
    (c : ι → ℝ) (hc : ∀ i, 0 < c i) (θ₁ θ₂ : ℝ) (hθ₁ : 0 < θ₁) (hθ : θ₁ ≤ θ₂)
    (s₁ s₂ : ι → ℕ) (hs₁ : ∀ i, IsLeast (stockSet (d i) (c i) θ₁) (s₁ i))
    (hs₂ : ∀ i, IsLeast (stockSet (d i) (c i) θ₂) (s₂ i)) :
    (∀ i, s₂ i ≤ s₁ i) ∧ totalInvestment d c s₂ ≤ totalInvestment d c s₁ := by sorry

end ServiceParts.StockLevels

