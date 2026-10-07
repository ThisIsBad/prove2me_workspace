import Mathlib
import Definitions.Def_FibHeap_Amort_Model

namespace FibHeap.Amort
theorem corollary_1 (s : Coll) (hs : Reachable s) :
    ∀ r ∈ s, ∀ τ ∈ r, ∀ x ∈ τ.subtrees,
      Nat.fib (x.rank + 2) ≤ x.size ∧
        Real.goldenRatio ^ x.rank ≤ (Nat.fib (x.rank + 2) : ℝ) := by sorry
end FibHeap.Amort

