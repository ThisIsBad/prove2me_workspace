import Mathlib
import Definitions.Def_FibHeap_Amort_Model

namespace FibHeap.Amort
theorem lemma_1 (s : Coll) (hs : Reachable s) :
    ∀ r ∈ s, ∀ τ ∈ r, ∀ x ∈ τ.subtrees, ∀ (j : ℕ) (hj : j < x.children.length),
      j + 1 ≤ (x.children[j]'hj).rank + 2 := by sorry
end FibHeap.Amort

