import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph
import Definitions.Def_PathsTreesFlowers_Invariance_Basic
import Definitions.Def_PathsTreesFlowers_Invariance_Shrink
import Definitions.Def_PathsTreesFlowers_Invariance_Config

namespace PathsTreesFlowers.Invariance

/-- 6.2 (c), p. 464: `G*` is obtained from `G` by shrinking the connected components of `O(G)⁺`.
Two vertices lie in the same part of `P` (the same vertex of `G*`) iff they are equal or both
lie in `O(G)` and are joined by a sequence of edges of `G` with all end-points in `O(G)`. -/
theorem theorem_6_2_c {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E)
    (M : Finset E) (C : Config60 G M) :
    ∀ u v : V, C.P.part u = C.P.part v ↔
      (u = v ∨ (u ∈ outerSet C ∧ v ∈ outerSet C ∧
        Relation.ReflTransGen
          (fun x y => x ∈ outerSet C ∧ y ∈ outerSet C ∧ ∃ e : E, G.ends e = s(x, y)) u v)) := by sorry

end PathsTreesFlowers.Invariance

