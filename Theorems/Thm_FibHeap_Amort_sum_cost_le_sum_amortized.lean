import Mathlib
import Definitions.Def_FibHeap_Amort_Model

namespace FibHeap.Amort
theorem sum_cost_le_sum_amortized (T : ℕ) (s : ℕ → Coll) (op : ℕ → Op) (d : ℕ → StepData)
    (hrun : IsRun T s op d) :
    (∑ t ∈ Finset.range T, (cost (d t) : ℤ)) ≤
      ∑ t ∈ Finset.range T, amortized (d t) (s t) (s (t + 1)) := by sorry
end FibHeap.Amort

