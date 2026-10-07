import Mathlib
import Definitions.Def_BellmanDP_GoldMining_Model

namespace BellmanDP.GoldMining

/-- Bellman, *Dynamic Programming*, Ch. II, Theorem 7, p. 76: for `0 ≤ p₁, p₂ < 1`,
`0 ≤ r₁, r₂ ≤ 1`, let `f` be the solution of (5.1) and `g` the solution of the perturbed
equation (2), both in the class of functions bounded in every rectangle, with `h` bounded in every
rectangle (the hypothesis under which (2) has a solution in that class). Then in any rectangle
`R: 0 ≤ x ≤ X̄, 0 ≤ y ≤ Ȳ`, `|f(x, y) − g(x, y)| ≤ Max_R |h(x, y)| / q` with
`q = Min((1 − p₁), (1 − p₂))`; the maximum of `|h|` over `R` is written as an arbitrary bound `M`
of `|h|` on `R`. -/
theorem stability (p₁ p₂ r₁ r₂ : ℝ)
    (hp₁0 : 0 ≤ p₁) (hp₁1 : p₁ < 1) (hp₂0 : 0 ≤ p₂) (hp₂1 : p₂ < 1)
    (hr₁0 : 0 ≤ r₁) (hr₁1 : r₁ ≤ 1) (hr₂0 : 0 ≤ r₂) (hr₂1 : r₂ ≤ 1)
    (h : ℝ → ℝ → ℝ) (hh : BoundedOnRectangles h)
    (f : ℝ → ℝ → ℝ) (hf : IsGoldMiningSolution p₁ p₂ r₁ r₂ f) (hfb : BoundedOnRectangles f)
    (g : ℝ → ℝ → ℝ) (hg : IsPerturbedSolution p₁ p₂ r₁ r₂ h g) (hgb : BoundedOnRectangles g)
    (X Y M : ℝ) (hM : ∀ x y : ℝ, 0 ≤ x → x ≤ X → 0 ≤ y → y ≤ Y → |h x y| ≤ M) :
    ∀ x y : ℝ, 0 ≤ x → x ≤ X → 0 ≤ y → y ≤ Y →
      |f x y - g x y| ≤ M / min (1 - p₁) (1 - p₂) := by sorry

end BellmanDP.GoldMining

