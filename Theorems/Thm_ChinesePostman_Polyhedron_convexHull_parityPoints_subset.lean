import Mathlib
import Definitions.Def_ChinesePostman_Polyhedron_Setting

namespace ChinesePostman.Polyhedron

theorem convexHull_parityPoints_subset {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : Graph V E) :
    convexHull ℝ (parityPoints G) ⊆ postmanPolyhedron G := by sorry

end ChinesePostman.Polyhedron

