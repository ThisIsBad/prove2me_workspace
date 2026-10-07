import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph
import Definitions.Def_PathsTreesFlowers_Duality_Basic
import Definitions.Def_PathsTreesFlowers_Duality_OddSetCover

namespace PathsTreesFlowers.Duality

theorem lemma_5_7 {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E)
    (M : Finset E) (hM : EdmondsMatching65.Polyhedron.IsMatching G M)
    (hexp : (Finset.univ.filter (IsExposed G M)).card ≤ 1) :
    ∃ S : Finset (Finset V), IsOddSetCover G S ∧ capacitySum S = M.card := by sorry

end PathsTreesFlowers.Duality

