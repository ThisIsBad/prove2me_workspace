import Mathlib
import Definitions.Def_ChvatalArtGallery_FanPartition_Triangulation

namespace ChvatalArtGallery.FanPartition

/-- Proof of the Theorem, p. 40: every n-triangulation with 3 ≤ n ≤ 5 is a fan. -/
theorem small_triangulation_is_fan (n : ℕ) (hn3 : 3 ≤ n) (hn5 : n ≤ 5)
    (D : Finset (Sym2 (Fin n))) (hD : IsTriangulation n D) :
    IsFan n D (triangles n D) := by sorry

end ChvatalArtGallery.FanPartition

