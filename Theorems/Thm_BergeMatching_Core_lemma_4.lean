import Mathlib
import Definitions.Def_BergeMatching_Core_AlternatingChain
import Definitions.Def_BergeMatching_Core_Arrows

namespace BergeMatching.Core

/-- Berge (1957), p. 843, Lemma 4: let `Z` be a connected component of the subgraph induced
on the inaccessible points `I`; if `ā` is inaccessible, every edge with exactly one endpoint in
`Z` is weak and carries no arrow, every vertex outside `Z` joined to `Z` by an edge is a weak
point, and `|Z| ≥ 2`. -/
theorem lemma_4 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : G.Subgraph) (hM : M.IsMatching) (h : AbarInaccessible G M)
    (Z : (G.induce {x : V | IsInaccessible G M x}).ConnectedComponent) :
    (∀ z ∈ Subtype.val '' Z.supp, ∀ w : V, w ∉ Subtype.val '' Z.supp → G.Adj z w →
        s(z, w) ∉ M.edgeSet ∧ ¬ Arrow G M (some z) (some w) ∧ ¬ Arrow G M (some w) (some z) ∧
          IsWeakPt G M w) ∧
      2 ≤ (Subtype.val '' Z.supp).ncard := by sorry

end BergeMatching.Core

