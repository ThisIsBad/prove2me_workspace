import Mathlib
import Definitions.Def_WeylPolyhedra_Polyhedron_Polytope

namespace WeylPolyhedra.Polyhedron

/-- Weyl (1935), §4 II, pp. 302–303: finitely many inequalities
`(α x) ≡ α₁x₁ + ⋯ + α_{n-1}x_{n-1} - α_n ≥ 0` on `R̄_{n-1} = ℝᵐ` (row `j` has normal
`A j = (α₁, …, α_{n-1})` and constant `b j = α_n`) cut out a region `H`. `H` is a convex
polyhedron (the convex hull of a finite non-degenerate point system) if and only if
(i) every point `π' ∈ ℝᵐ` is a nonnegative linear combination of the normals `A j`, and
(ii) `H` has an inner point: some `c` satisfies every inequality strictly.
Added hypothesis (p. 291: a half-space is given by a nonzero point of the dual space): every
row `(A j, b j)` is nonzero. -/
theorem isConvexPolyhedron_iff {m : ℕ} {J : Type*} [Fintype J] (A : J → Fin m → ℝ)
    (b : J → ℝ) (hrow : ∀ j, A j ≠ 0 ∨ b j ≠ 0) :
    IsConvexPolyhedron (inequalityRegion A b) ↔
      ((∀ π' : Fin m → ℝ, ∃ ν : J → ℝ, (∀ j, 0 ≤ ν j) ∧ π' = ∑ j, ν j • A j) ∧
        ∃ c : Fin m → ℝ, ∀ j, 0 < A j ⬝ᵥ c - b j) := by sorry

end WeylPolyhedra.Polyhedron

