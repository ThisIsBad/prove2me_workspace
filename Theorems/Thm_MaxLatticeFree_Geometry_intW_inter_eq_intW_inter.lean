import Mathlib
import Definitions.Def_MaxLatticeFree_Geometry_intW

namespace MaxLatticeFree.Geometry

theorem intW_inter_eq_intW_inter {n : ℕ} (V W : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (hVW : V ≤ W)
    (S : Set (EuclideanSpace ℝ (Fin n))) (hSW : S ⊆ (W : Set (EuclideanSpace ℝ (Fin n)))) (hS : Convex ℝ S)
    (hne : (intW (W : Set (EuclideanSpace ℝ (Fin n))) S ∩ (V : Set (EuclideanSpace ℝ (Fin n)))).Nonempty) :
    intW (W : Set (EuclideanSpace ℝ (Fin n))) S ∩ (V : Set (EuclideanSpace ℝ (Fin n))) =
      intW (V : Set (EuclideanSpace ℝ (Fin n))) (S ∩ (V : Set (EuclideanSpace ℝ (Fin n)))) := by sorry

end MaxLatticeFree.Geometry
