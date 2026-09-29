import Mathlib

open scoped InnerProductSpace

namespace OnlineConvexOpt.ProjectionFree

/-- `f` is `β`-smooth on `K` with gradient map `g`: for every `x y ∈ K`,
`f y ≤ f x + ⟪g x, y - x⟫_ℝ + (β / 2) * ‖y - x‖ ^ 2` (Hazan, *Introduction to Online Convex
Optimization*, 2nd ed., arXiv:1909.05207v3, p. 18, PDF p. 40; used again in this chapter, e.g.
p. 127 Theorem 7.1, p. 134 "the functions `Ft` are 1-smooth"). Redeclared here (not imported)
since Chapter II's `ConvexBasics.SmoothOn` is not yet a published series definition; see
`MODERATION_NOTES.md`. -/
def SmoothOn {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K : Set E) (f : E → ℝ) (g : E → E) (β : ℝ) : Prop :=
  ∀ x ∈ K, ∀ y ∈ K, f y ≤ f x + ⟪g x, y - x⟫_ℝ + (β / 2) * ‖y - x‖ ^ 2

end OnlineConvexOpt.ProjectionFree
