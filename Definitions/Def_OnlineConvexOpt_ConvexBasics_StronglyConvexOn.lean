import Mathlib

open scoped InnerProductSpace

namespace OnlineConvexOpt.ConvexBasics

/-- `f` is `α`-strongly convex on `K` with gradient map `g`: for every `x y ∈ K`,
`f y ≥ f x + ⟪g x, y - x⟫_ℝ + (α / 2) * ‖y - x‖ ^ 2` (Hazan, *Introduction to Online Convex
Optimization*, 2nd ed., arXiv:1909.05207v3, p. 18, PDF p. 40). `g x` stands for the book's
`∇f(x)`. -/
def StronglyConvexOn {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K : Set E) (f : E → ℝ) (g : E → E) (α : ℝ) : Prop :=
  ∀ x ∈ K, ∀ y ∈ K, f y ≥ f x + ⟪g x, y - x⟫_ℝ + (α / 2) * ‖y - x‖ ^ 2

end OnlineConvexOpt.ConvexBasics
