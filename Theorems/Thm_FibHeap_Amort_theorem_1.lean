import Mathlib
import Definitions.Def_FibHeap_Amort_Model

namespace FibHeap.Amort
theorem theorem_1 :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : ℕ) (s : ℕ → Coll) (op : ℕ → Op) (d : ℕ → StepData),
      IsRun T s op d →
        (∑ t ∈ Finset.range T, (cost (d t) : ℝ)) ≤
          ∑ t ∈ Finset.range T, opBound C (s t) (op t) := by sorry
end FibHeap.Amort

