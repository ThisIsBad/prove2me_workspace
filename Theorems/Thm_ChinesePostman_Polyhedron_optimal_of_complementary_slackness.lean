import Mathlib
import Definitions.Def_ChinesePostman_Polyhedron_Setting

namespace ChinesePostman.Polyhedron

theorem optimal_of_complementary_slackness {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : Graph V E) (c : E → ℝ)
    (x : E → ℝ) (hx : x ∈ postmanPolyhedron G)
    (y : Finset V → ℝ) (hy : IsDualFeasible G c y)
    (h311 : ∀ e, 0 < x e → dualLoad G y e = c e)
    (h312 : ∀ S ∈ oddSets G, 0 < y S → cutSum G x S = 1) :
    (∀ x' ∈ postmanPolyhedron G, objective c x ≤ objective c x') ∧
      (∀ y' : Finset V → ℝ, IsDualFeasible G c y' → dualValue G y' ≤ dualValue G y) := by sorry

end ChinesePostman.Polyhedron

