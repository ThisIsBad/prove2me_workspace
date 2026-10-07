import Mathlib
import Definitions.Def_FibHeap_Amort_Model

namespace FibHeap.Amort
theorem potential_decreaseKey_le (s s' : Coll) (Δ : ℝ) (i h : ℕ) (d : StepData)
    (hstep : Step s (.decreaseKey Δ i h) s' d) :
    potential s' + d.cascading ≤ potential s + 3 := by sorry
end FibHeap.Amort

