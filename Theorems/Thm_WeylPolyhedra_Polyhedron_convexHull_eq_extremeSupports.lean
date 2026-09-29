import Mathlib
import Definitions.Def_WeylPolyhedra_Polyhedron_Polytope

namespace WeylPolyhedra.Polyhedron

/-- Weyl (1935), §4 I, p. 301, in affine form (`R̄_{n-1} = ℝᵐ`, a point `x` standing for
`(x, -1)`): let `S ⊆ ℝᵐ` be a finite non-degenerate point system (its affine span is the whole
space). Then `S` has at least one extreme support, and the convex hull `H` of `S` — the convex
polyhedron arising from `S` — is characterized by the extreme support inequalities: `H` is the
set of points satisfying `a ⬝ᵥ x - a₀ ≥ 0` for every extreme support `(a, a₀)` of `S`. -/
theorem convexHull_eq_extremeSupports {m : ℕ} (S : Finset (Fin m → ℝ))
    (hS : affineSpan ℝ (S : Set (Fin m → ℝ)) = ⊤) :
    (∃ (a : Fin m → ℝ) (a₀ : ℝ), IsExtremeAffineSupport S a a₀) ∧
      convexHull ℝ (S : Set (Fin m → ℝ)) =
        {x | ∀ (a : Fin m → ℝ) (a₀ : ℝ), IsExtremeAffineSupport S a a₀ → 0 ≤ a ⬝ᵥ x - a₀} := by sorry

end WeylPolyhedra.Polyhedron

