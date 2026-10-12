import Mathlib
import Definitions.Def_KarpPapadimitriou_SmallFacial_COP

namespace KarpPapadimitriou.SmallFacial

/-- p. 6, proof of Lemma 1: zero-one hulls have zero-one vertices and no rays. -/
theorem zero_one_vertices (C : COP) (hC : IsZeroOne C) (z : List Bool) (hz : z ∈ C.L) :
    (∀ v, IsVertex (hull C z) v → ∀ i, v i = 0 ∨ v i = 1) ∧
    ¬ HasRay (hull C z) := by sorry

end KarpPapadimitriou.SmallFacial

