import Mathlib
import Definitions.Def_McNaughtonSched_SingleProc_Model

namespace McNaughtonSched.SingleProc

theorem pair_interchange {m : ℕ} (a p d : Fin m → ℝ) (i j : Fin m)
    (hai : 0 < a i) (haj : 0 < a j) (hr : p j / a j < p i / a i)
    (t : ℝ) (hdi : d i ≤ t) (hdj : d j ≤ t) :
    taskLoss p d i (t + a i) + taskLoss p d j (t + a i + a j) <
      taskLoss p d j (t + a j) + taskLoss p d i (t + a j + a i) := by sorry

end McNaughtonSched.SingleProc

