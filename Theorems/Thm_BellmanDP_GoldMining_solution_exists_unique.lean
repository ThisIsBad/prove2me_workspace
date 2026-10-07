import Mathlib
import Definitions.Def_BellmanDP_GoldMining_Model

namespace BellmanDP.GoldMining

/-- Bellman, *Dynamic Programming*, Ch. II, Theorem 1, p. 64: if `|p₁|, |p₂| < 1` and
`0 ≤ r₁, r₂ < 1`, there is a unique solution of (5.1) which is bounded in any rectangle
`0 ≤ x ≤ X̄, 0 ≤ y ≤ Ȳ`, and this solution is continuous on the closed quadrant `x, y ≥ 0`.
Uniqueness is equality on the quadrant, where (5.1) is posed. -/
theorem solution_exists_unique (p₁ p₂ r₁ r₂ : ℝ)
    (hp₁ : |p₁| < 1) (hp₂ : |p₂| < 1)
    (hr₁0 : 0 ≤ r₁) (hr₁1 : r₁ < 1) (hr₂0 : 0 ≤ r₂) (hr₂1 : r₂ < 1) :
    ∃ f : ℝ → ℝ → ℝ, IsGoldMiningSolution p₁ p₂ r₁ r₂ f ∧ BoundedOnRectangles f ∧
      ContinuousOn (Function.uncurry f) (Set.Ici (0 : ℝ) ×ˢ Set.Ici (0 : ℝ)) ∧
      ∀ g : ℝ → ℝ → ℝ, IsGoldMiningSolution p₁ p₂ r₁ r₂ g → BoundedOnRectangles g →
        ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → g x y = f x y := by sorry

end BellmanDP.GoldMining

