import Mathlib
import Definitions.Def_FibHeap_Amort_Model

namespace FibHeap.Amort
theorem potential_deleteMin_le (s s' : Coll) (hs : Reachable s) (h : ℕ) (d : StepData)
    (hstep : Step s (.deleteMin h) s' d) :
    (potential s' : ℝ) ≤
      potential s + Real.logb Real.goldenRatio (heapSize (s.getD h [])) - d.links := by sorry
end FibHeap.Amort

