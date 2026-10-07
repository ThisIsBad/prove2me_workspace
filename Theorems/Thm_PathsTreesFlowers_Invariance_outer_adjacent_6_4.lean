import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph
import Definitions.Def_PathsTreesFlowers_Invariance_Basic
import Definitions.Def_PathsTreesFlowers_Invariance_Shrink
import Definitions.Def_PathsTreesFlowers_Invariance_Config

namespace PathsTreesFlowers.Invariance

/-- 6.4, p. 464: each outer vertex `u` of `G` is joined only to inner vertices and to other
vertices in the complete expansion of its image `u*`; and each inner vertex is joined to an outer
vertex of `G`. -/
theorem outer_adjacent_6_4 {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E)
    (M : Finset E) (C : Config60 G M) :
    (∀ u ∈ outerSet C, ∀ (e : E) (w : V), G.ends e = s(u, w) →
      w ∈ innerSet C ∨ C.P.part w = C.P.part u) ∧
    (∀ v ∈ innerSet C, ∃ u ∈ outerSet C, ∃ e : E, G.ends e = s(u, v)) := by sorry

end PathsTreesFlowers.Invariance

