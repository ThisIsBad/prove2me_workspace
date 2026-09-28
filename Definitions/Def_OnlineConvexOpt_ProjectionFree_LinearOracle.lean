import Mathlib

open scoped InnerProductSpace

namespace OnlineConvexOpt.ProjectionFree

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `v` solves the linear-minimization oracle over `K` in direction `grad` (Algorithm 25 line 3,
Algorithm 27 line 5, Hazan, *Introduction to Online Convex Optimization*, 2nd ed.,
arXiv:1909.05207v3, p. 126, PDF p. 148, Eq. (7.4)): `v ∈ K` minimizes the linear functional
`x ↦ ⟪grad, x⟫` over `K`. This is the "projection-free" step: a linear optimization oracle call
in place of a Euclidean projection. -/
def IsLinearMinimizer (K : Set E) (grad v : E) : Prop :=
  v ∈ K ∧ ∀ x ∈ K, ⟪grad, v⟫_ℝ ≤ ⟪grad, x⟫_ℝ

end OnlineConvexOpt.ProjectionFree
