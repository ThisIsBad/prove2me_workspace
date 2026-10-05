import Mathlib
import Definitions.Def_BergeMatching_Core_AlternatingChain
import Definitions.Def_BergeMatching_Core_Arrows

namespace BergeMatching.Core

/-- Berge (1957), p. 843, Lemma 3: if `ā` is inaccessible, `M = ∅` (no medium point) and
`I = ∅` (no inaccessible point), then `S ∪ N` is a maximum internally stable set, `W` is a
minimum cover, and `V₀` is a maximum matching. -/
theorem lemma_3 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : G.Subgraph) (hM : M.IsMatching) (h : AbarInaccessible G M)
    (hMed : {x : V | IsMedium G M x} = ∅) (hI : {x : V | IsInaccessible G M x} = ∅) :
    IsMaximumIndepSet G ({x : V | IsStrongPt G M x} ∪ {x : V | IsNeutral M x}) ∧
      IsMinimumVertexCover G {x : V | IsWeakPt G M x} ∧
      IsMaximumMatching M := by sorry

end BergeMatching.Core

