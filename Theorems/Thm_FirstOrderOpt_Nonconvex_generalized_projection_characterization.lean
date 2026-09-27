import Mathlib

namespace FirstOrderOpt.Nonconvex

open scoped RealInnerProductSpace

/-- Lemma 6.6. `xPlus` is the generalized projection (6.2.6). Then for every `u ∈ X`,
`⟨g,xPlus⟩ + h(xPlus) + (1/γ)V(x,xPlus) ≤ ⟨g,u⟩ + h(u) + (1/γ)[V(x,u) - V(xPlus,u)]`. -/
theorem generalized_projection_characterization {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (X : Set E) (h : E → ℝ) (V : E → E → ℝ)
    (x xPlus g : E) (γ : ℝ) (hγ : 0 < γ) (hx : x ∈ X) (hxPlus : xPlus ∈ X)
    (hmin : ∀ u ∈ X, ⟪g, xPlus⟫ + (1 / γ) * V x xPlus + h xPlus ≤
      ⟪g, u⟫ + (1 / γ) * V x u + h u) :
    ∀ u ∈ X, ⟪g, xPlus⟫ + h xPlus + (1 / γ) * V x xPlus ≤
      ⟪g, u⟫ + h u + (1 / γ) * (V x u - V xPlus u) := by sorry

end FirstOrderOpt.Nonconvex

