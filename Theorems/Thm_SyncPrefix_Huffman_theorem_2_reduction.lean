import Mathlib
import Definitions.Def_SyncPrefix_Huffman_Constructions

namespace SyncPrefix.Huffman

open SetCoverThreshold.SetCover

/-- Theorem 2's reduction (p. 5): for a Set Cover instance in which every point lies in some set,
the pipe automaton has `p² + 1` states and one letter per set, is strongly acyclic and
synchronizing, and the length of its shortest synchronizing word is the minimum size of a set
cover. -/
theorem theorem_2_reduction (I : SCInstance) (hI : I.Coverable) :
    (scAutomaton I).n = I.n ^ 2 + 1 ∧ (scAutomaton I).k = I.sets.length ∧
      StronglyAcyclic (scAutomaton I).δ ∧ IsSynchronizing (scAutomaton I).δ ∧
        syncLength (scAutomaton I).δ = minCover I := by sorry

end SyncPrefix.Huffman

