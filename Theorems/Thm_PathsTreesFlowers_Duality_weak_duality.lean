import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph
import Definitions.Def_PathsTreesFlowers_Duality_OddSetCover

namespace PathsTreesFlowers.Duality

theorem weak_duality {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E)
    (M : Finset E) (S : Finset (Finset V))
    (hM : EdmondsMatching65.Polyhedron.IsMatching G M) (hS : IsOddSetCover G S) :
    M.card ≤ capacitySum S := by sorry

end PathsTreesFlowers.Duality

