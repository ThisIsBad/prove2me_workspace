import Mathlib
import Definitions.Def_FibHeap_Amort_Model

namespace FibHeap.Amort
theorem rank_le_logb (s : Coll) (hs : Reachable s) :
    ∀ r ∈ s, ∀ τ ∈ r, ∀ x ∈ τ.subtrees,
      Real.goldenRatio ^ x.rank ≤ (heapSize r : ℝ) ∧
        (x.rank : ℝ) ≤ Real.logb Real.goldenRatio (heapSize r) := by sorry
end FibHeap.Amort

