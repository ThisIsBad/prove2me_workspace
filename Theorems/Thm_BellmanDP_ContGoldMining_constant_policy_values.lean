import Mathlib
import Definitions.Def_BellmanDP_ContGoldMining_Process

namespace BellmanDP.ContGoldMining

/-- Bellman, *Dynamic Programming*, Ch. VIII, § 10, Eq. (10.1), pp. 230–231: using `A` for all
`t ≥ 0` yields `f_A(∞) = r₁ x₀/(q₁ + r₁)`, and using `B` for all `t ≥ 0` yields
`f_B(∞) = r₂ y₀/(q₂ + r₂)`. -/
theorem constant_policy_values (q₁ q₂ r₁ r₂ x₀ y₀ : ℝ) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hx₀ : 0 ≤ x₀) (hy₀ : 0 ≤ y₀) :
    goldInfty (Params.two q₁ q₂ r₁ r₂) x₀ y₀ (twoChoice fun _ => 1) =
        ENNReal.ofReal (r₁ * x₀ / (q₁ + r₁)) ∧
      goldInfty (Params.two q₁ q₂ r₁ r₂) x₀ y₀ (twoChoice fun _ => 0) =
        ENNReal.ofReal (r₂ * y₀ / (q₂ + r₂)) := by sorry

end BellmanDP.ContGoldMining

