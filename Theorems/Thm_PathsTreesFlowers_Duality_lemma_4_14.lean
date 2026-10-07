import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph
import Definitions.Def_PathsTreesFlowers_Duality_Basic
import Definitions.Def_PathsTreesFlowers_Duality_Shrink

namespace PathsTreesFlowers.Duality

theorem lemma_4_14 {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E)
    (vs : List V) (es : List E) (hB : IsCircuit G vs es) (hodd : Odd vs.length)
    (M₁ : Finset {e : E // ¬ InsidePart G (blockPartition vs.toFinset) e})
    (hM₁ : EdmondsMatching65.Polyhedron.IsMatching (shrink G (blockPartition vs.toFinset)) M₁) :
    ∃ MB : Finset E, IsMaxMatchingOn G es.toFinset MB ∧
      EdmondsMatching65.Polyhedron.IsMatching G
        (M₁.map (Function.Embedding.subtype _) ∪ MB) := by sorry

end PathsTreesFlowers.Duality

