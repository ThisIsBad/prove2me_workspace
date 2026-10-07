import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph
import Definitions.Def_PathsTreesFlowers_Invariance_Basic
import Definitions.Def_PathsTreesFlowers_Invariance_Shrink
import Definitions.Def_PathsTreesFlowers_Invariance_Config

namespace PathsTreesFlowers.Invariance

/-- 6.2 (b), p. 464: the inner vertices `I(G)` are precisely the vertices of `G` not in `O(G)`
but joined to vertices in `O(G)`. -/
theorem theorem_6_2_b {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E)
    (M : Finset E) (C : Config60 G M) :
    ∀ v : V, v ∈ innerSet C ↔ v ∉ outerSet C ∧ ∃ u ∈ outerSet C, ∃ e : E, G.ends e = s(u, v) := by sorry

end PathsTreesFlowers.Invariance

