import Mathlib
import Definitions.Def_CachonCoord_InternalMarket_Revenue

namespace CachonCoord.InternalMarket

/-- §6.9.1, pp. 93–94 (Cachon 2003, 3rd draft): when the supplier charges
`w(α, Q) = ((η − 1)/η)(α₁^η + α₂^η)^{1/η} Q^{−1/η}` (`α₁, α₂ > 0`, `η > 1`, `Q > 0`),
1. retailer one's unique optimal quantity over `[0, ∞)` is `γ°(α) Q` and retailer two's is
   `(1 − γ°(α)) Q`, so the retailers order exactly `Q` units in total;
2. this allocation maximizes the retailers' total revenue `α₁ q₁^{(η−1)/η} + α₂ q₂^{(η−1)/η}` over all
   allocations `q₁, q₂ ≥ 0` with `q₁ + q₂ ≤ Q`. -/
theorem p94_market_allocation (η α₁ α₂ Q : ℝ) (hη : 1 < η) (hα₁ : 0 < α₁) (hα₂ : 0 < α₂)
    (hQ : 0 < Q) :
    (∀ q : ℝ, 0 ≤ q →
      (IsMaxOn (retailerProfit η α₁ (price η α₁ α₂ Q)) (Set.Ici 0) q ↔
        q = optShare η α₁ α₂ * Q)) ∧
    (∀ q : ℝ, 0 ≤ q →
      (IsMaxOn (retailerProfit η α₂ (price η α₁ α₂ Q)) (Set.Ici 0) q ↔
        q = (1 - optShare η α₁ α₂) * Q)) ∧
    optShare η α₁ α₂ * Q + (1 - optShare η α₁ α₂) * Q = Q ∧
    ∀ q₁ q₂ : ℝ, 0 ≤ q₁ → 0 ≤ q₂ → q₁ + q₂ ≤ Q →
      α₁ * q₁ ^ ((η - 1) / η) + α₂ * q₂ ^ ((η - 1) / η) ≤
        α₁ * (optShare η α₁ α₂ * Q) ^ ((η - 1) / η) +
          α₂ * ((1 - optShare η α₁ α₂) * Q) ^ ((η - 1) / η) := by sorry

end CachonCoord.InternalMarket

