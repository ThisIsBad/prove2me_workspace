import Mathlib
import Definitions.Def_BergeMatching_Core_AlternatingChain
import Definitions.Def_BergeMatching_Core_Arrows

namespace BergeMatching.Core

/-- Berge (1957), p. 843, Lemma 2: if `ā` is inaccessible, `S ∪ N` is internally stable. -/
theorem lemma_2 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : G.Subgraph) (hM : M.IsMatching) (h : AbarInaccessible G M) :
    G.IsIndepSet ({x : V | IsStrongPt G M x} ∪ {x : V | IsNeutral M x}) := by sorry

end BergeMatching.Core

