import Mathlib
import Definitions.Def_BellmanDP_GoldMining_Model

namespace BellmanDP.GoldMining

/-- Bellman, *Dynamic Programming*, Ch. II, Theorem 2, p. 69: for `0 ≤ p₁, p₂ < 1`,
`0 ≤ r₁, r₂ ≤ 1`, the solution `f` of (9) (the solution bounded in every rectangle) satisfies, at
every `x, y ≥ 0`: `f = A`-branch when `p₁ r₁ x/(1 − p₁) > p₂ r₂ y/(1 − p₂)`, `f = B`-branch when
the reverse strict inequality holds, and both branches equal `f` (either choice is optimal) on
equality. -/
theorem index_rule_two_mines (p₁ p₂ r₁ r₂ : ℝ)
    (hp₁0 : 0 ≤ p₁) (hp₁1 : p₁ < 1) (hp₂0 : 0 ≤ p₂) (hp₂1 : p₂ < 1)
    (hr₁0 : 0 ≤ r₁) (hr₁1 : r₁ ≤ 1) (hr₂0 : 0 ≤ r₂) (hr₂1 : r₂ ≤ 1)
    (f : ℝ → ℝ → ℝ) (hf : IsGoldMiningSolution p₁ p₂ r₁ r₂ f) (hfb : BoundedOnRectangles f)
    (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (p₂ * r₂ * y / (1 - p₂) < p₁ * r₁ * x / (1 - p₁) → f x y = goldA p₁ r₁ f x y) ∧
    (p₁ * r₁ * x / (1 - p₁) < p₂ * r₂ * y / (1 - p₂) → f x y = goldB p₂ r₂ f x y) ∧
    (p₁ * r₁ * x / (1 - p₁) = p₂ * r₂ * y / (1 - p₂) →
      f x y = goldA p₁ r₁ f x y ∧ f x y = goldB p₂ r₂ f x y) := by sorry

end BellmanDP.GoldMining

