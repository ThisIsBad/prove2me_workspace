import Mathlib
import Definitions.Def_SocialEquilibrium_Existence_IsPolyhedron

namespace SocialEquilibrium.Existence

/-- Debreu (1952), §1, p. 887: the product of two convex cells `A ⊆ ℝˡ`, `B ⊆ ℝᵐ` is a convex
cell in `ℝˡ⁺ᵐ`. -/
theorem isConvexCell_prod {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {A : Set E} {B : Set F} (hA : IsConvexCell A) (hB : IsConvexCell B) :
    IsConvexCell (A ×ˢ B) := by sorry

end SocialEquilibrium.Existence
