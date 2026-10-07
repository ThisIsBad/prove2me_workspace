import Mathlib
import Definitions.Def_CachonCoord_InternalMarket_Revenue

namespace CachonCoord.InternalMarket

/-- §6.9.1, p. 93, the display after (44) (Cachon 2003, 3rd draft): conditional on the optimal
allocation, the retailers' total revenue is
`π(α, Q) = π(γ°(α), α, Q) = (α₁^η + α₂^η)^{1/η} Q^{(η−1)/η}`, for `α₁, α₂ > 0`, `η > 1`, `Q ≥ 0`. -/
theorem p93_optimal_revenue (η α₁ α₂ Q : ℝ) (hη : 1 < η) (hα₁ : 0 < α₁) (hα₂ : 0 < α₂)
    (hQ : 0 ≤ Q) :
    optRevenue η α₁ α₂ Q = (α₁ ^ η + α₂ ^ η) ^ (1 / η) * Q ^ ((η - 1) / η) := by sorry

end CachonCoord.InternalMarket

