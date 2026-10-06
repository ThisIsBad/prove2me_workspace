import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph
import Definitions.Def_EdmondsMatching65_Polyhedron_MatchingPolyhedron

namespace EdmondsMatching65.Polyhedron

theorem theorem_P_of_linear_forms {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (G : Graph V E)
    (h : ∀ c : E → ℝ, ∃ x ∈ matchingPolyhedron G, (∀ e, x e = 0 ∨ x e = 1) ∧
      ∀ x' ∈ matchingPolyhedron G, W c x' ≤ W c x) :
    Set.extremePoints ℝ (matchingPolyhedron G) = matchingVectors G := by sorry

end EdmondsMatching65.Polyhedron

