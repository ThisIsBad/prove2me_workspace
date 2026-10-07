import Mathlib
import Definitions.Def_ChinesePostman_Polyhedron_Setting

namespace ChinesePostman.Polyhedron

theorem weak_duality {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : Graph V E) (c : E → ℝ)
    (x : E → ℝ) (hx : x ∈ postmanPolyhedron G)
    (y : Finset V → ℝ) (hy : IsDualFeasible G c y) :
    dualValue G y ≤ objective c x := by sorry

end ChinesePostman.Polyhedron

