import Mathlib
import Definitions.Def_OnlineConvexOpt_SecondOrder_ExpConcave

open OnlineConvexOpt.SecondOrder

namespace OnlineConvexOpt.SecondOrder

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Lemma 4.3 (Hazan, *Introduction to Online Convex Optimization*, 2nd ed.,
arXiv:1909.05207v3, p. 59, PDF p. 81). Let `f : K → ℝ` be `α`-exp-concave, `D` the diameter of
`K` and `G` a bound on the (sub)gradients of `f` over `K` (`hG`, stated via `HasGradientAt` as
in `OnlineConvexOpt.FirstOrder`). Then for all `γ ≤ (1/2) min{1/(GD), α}` and all `x, y ∈ K`,
`f(x) ≥ f(y) + ∇f(y)^⊤(x - y) + (γ/2)(x - y)^⊤∇f(y)∇f(y)^⊤(x - y)`, where the quadratic term
`(x - y)^⊤∇f(y)∇f(y)^⊤(x - y)` equals `(∇f(y)^⊤(x - y))²` since `∇f(y)∇f(y)^⊤` has rank one. -/
theorem exp_concave_quadratic_lower_bound (α D G γ : ℝ) (K : Set E) (f : E → ℝ)
    (hf : IsExpConcaveOn α K f) (hD : ∀ p ∈ K, ∀ q ∈ K, dist p q ≤ D)
    (hG : ∀ p ∈ K, ∀ v, HasGradientAt f v p → ‖v‖ ≤ G)
    (hγ : γ ≤ (1 / 2) * min (1 / (G * D)) α)
    (x y : E) (hx : x ∈ K) (hy : y ∈ K) (g : E) (hg : HasGradientAt f g y) :
    f y + inner ℝ g (x - y) + (γ / 2) * (inner ℝ g (x - y)) ^ 2 ≤ f x := by sorry

end OnlineConvexOpt.SecondOrder

