import Mathlib
import Definitions.Def_McNaughtonSched_SingleProc_Model

namespace McNaughtonSched.SingleProc

theorem loss_diff_ge_zero_deadline_diff {m : ℕ} (a p d : Fin m → ℝ)
    (ha : ∀ i, 0 < a i) (hp : ∀ i, 0 ≤ p i)
    (σ : Equiv.Perm (Fin m)) (hlate : ∀ i, d i ≤ completion (seqSchedule a σ) i)
    (S' : Schedule m) (hS' : IsFeasible a S') :
    totalLoss p 0 S' - totalLoss p 0 (seqSchedule a σ) ≤
      totalLoss p d S' - totalLoss p d (seqSchedule a σ) := by sorry

end McNaughtonSched.SingleProc

