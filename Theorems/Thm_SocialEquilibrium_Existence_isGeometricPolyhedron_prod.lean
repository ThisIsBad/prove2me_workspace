import Mathlib
import Definitions.Def_SocialEquilibrium_Existence_IsPolyhedron

namespace SocialEquilibrium.Existence

/-- Debreu (1952), §1, p. 887: the product of two geometric polyhedra is a geometric
polyhedron. -/
theorem isGeometricPolyhedron_prod {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {P : Set E} {Q : Set F} (hP : IsGeometricPolyhedron P) (hQ : IsGeometricPolyhedron Q) :
    IsGeometricPolyhedron (P ×ˢ Q) := by sorry

end SocialEquilibrium.Existence
