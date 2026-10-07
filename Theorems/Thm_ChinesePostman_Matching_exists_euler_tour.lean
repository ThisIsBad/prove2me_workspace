import Mathlib
import Definitions.Def_ChinesePostman_Matching_Setting

namespace ChinesePostman.Matching


/-- §2, p. 89: a connected even-degree multigraph has an Euler tour. -/
theorem exists_euler_tour
    {V E : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E) (hG : Connected G)
    (heven : ∀ v, Even (degree G v)) :
    ∃ ns : List V, ∃ es : List E, IsEulerTour G ns es := by sorry
end ChinesePostman.Matching

