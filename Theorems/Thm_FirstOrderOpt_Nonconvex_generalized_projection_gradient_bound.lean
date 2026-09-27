import Mathlib

namespace FirstOrderOpt.Nonconvex

open scoped RealInnerProductSpace

/-- Lemma 6.4. `xPlus` is the generalized projection (6.2.6): the minimizer over `X` of `u ↦
⟨g,u⟩ + (1/γ)V(x,u) + h(u)`. Writing `PXval := (1/γ)•(x-xPlus)` for the generalized projected
gradient `P_X(x,g,γ)` of (6.2.7), then `⟨g,PXval⟩ ≥ ‖PXval‖² + (1/γ)[h(xPlus)-h(x)]`. -/
theorem generalized_projection_gradient_bound {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (X : Set E) (h : E → ℝ) (V : E → E → ℝ)
    (x xPlus g : E) (γ : ℝ) (hγ : 0 < γ) (hx : x ∈ X) (hxPlus : xPlus ∈ X)
    (hmin : ∀ u ∈ X, ⟪g, xPlus⟫ + (1 / γ) * V x xPlus + h xPlus ≤
      ⟪g, u⟫ + (1 / γ) * V x u + h u)
    (PXval : E) (hPX : PXval = (1 / γ) • (x - xPlus)) :
    ⟪g, PXval⟫ ≥ ‖PXval‖ ^ 2 + (1 / γ) * (h xPlus - h x) := by sorry

end FirstOrderOpt.Nonconvex

