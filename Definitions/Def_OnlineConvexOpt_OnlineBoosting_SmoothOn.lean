import Mathlib

open scoped InnerProductSpace

namespace OnlineConvexOpt.OnlineBoosting

/-- `f` is `β`-smooth on `K` with gradient map `g` (Hazan, *Introduction to Online Convex
Optimization*, 2nd ed., arXiv:1909.05207v3, p. 18, PDF p. 40; used again p. 201, PDF p. 223,
"`f̂_t` is `dG/δ`-smooth"): for every `x y ∈ K`,
`f y ≤ f x + ⟪g x, y - x⟫_ℝ + (β / 2) * ‖y - x‖ ^ 2`. Redeclared here (not imported) since
Chapter II's own smoothness is not yet a published series definition. -/
def SmoothOn {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K : Set E) (f : E → ℝ) (g : E → E) (β : ℝ) : Prop :=
  ∀ x ∈ K, ∀ y ∈ K, f y ≤ f x + ⟪g x, y - x⟫_ℝ + (β / 2) * ‖y - x‖ ^ 2

end OnlineConvexOpt.OnlineBoosting
