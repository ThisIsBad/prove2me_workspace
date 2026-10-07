import Mathlib

open scoped InnerProductSpace

namespace OnlineConvexOpt.Blackwell

/-- The support function of a closed convex set `S` (Hazan, *Introduction to Online Convex
Optimization*, 2nd ed., arXiv:1909.05207v3, p. 210, PDF p. 232): `h_S(w) = max_{x∈S}{w^⊤x}`,
rendered as the real supremum of the image of `S` under `x ↦ ⟪w, x⟫` — a genuine maximum when
`S` is nonempty and compact, as the book's standing "closed, bounded" hypothesis on `S` ensures.
(The retired version used the binder `⨆ x ∈ S, …`, which on `ℝ` evaluates to the junk value
`sSup ∅ = 0` at every `x ∉ S` and so returned `max(h_S(w), 0)` instead of `h_S(w)`.) -/
noncomputable def SupportFunction {d : ℕ} (S : Set (EuclideanSpace ℝ (Fin d)))
    (w : EuclideanSpace ℝ (Fin d)) : ℝ :=
  sSup ((fun x => (⟪w, x⟫_ℝ : ℝ)) '' S)

end OnlineConvexOpt.Blackwell
