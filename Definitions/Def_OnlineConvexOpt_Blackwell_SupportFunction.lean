import Mathlib

open scoped InnerProductSpace

namespace OnlineConvexOpt.Blackwell

/-- The support function of a closed convex set `S` (Hazan, *Introduction to Online Convex
Optimization*, 2nd ed., arXiv:1909.05207v3, p. 210, PDF p. 232): `h_S(w) = max_{x∈S}{w^⊤x}`,
rendered as a real supremum (a genuine maximum when `S` is compact, as the book's standing
"closed, bounded" hypothesis on `S` ensures). -/
noncomputable def SupportFunction {d : ℕ} (S : Set (EuclideanSpace ℝ (Fin d)))
    (w : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ⨆ x ∈ S, (⟪w, x⟫_ℝ : ℝ)

end OnlineConvexOpt.Blackwell
