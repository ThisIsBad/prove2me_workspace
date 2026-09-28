import Mathlib
import Definitions.Def_SocialEquilibrium_Existence_IsPolyhedron

namespace SocialEquilibrium.Existence

end SocialEquilibrium.Existence

open SocialEquilibrium.Existence

theorem solution {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {A : Set E} {B : Set F} (hA : IsConvexCell A) (hB : IsConvexCell B) :
    IsConvexCell (A ×ˢ B) := by
  obtain ⟨s, hs, rfl⟩ := hA
  obtain ⟨t, ht, rfl⟩ := hB
  refine ⟨s ×ˢ t, hs.product ht, ?_⟩
  rw [Finset.coe_product, convexHull_prod]
