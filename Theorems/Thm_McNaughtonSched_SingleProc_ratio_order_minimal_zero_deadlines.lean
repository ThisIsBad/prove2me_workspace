import Mathlib
import Definitions.Def_McNaughtonSched_SingleProc_Model

namespace McNaughtonSched.SingleProc

theorem ratio_order_minimal_zero_deadlines {m : ℕ} (a p d : Fin m → ℝ)
    (ha : ∀ i, 0 < a i) (hp : ∀ i, 0 ≤ p i) (hd : ∀ i, d i = 0)
    (σ : Equiv.Perm (Fin m)) (hσ : InRatioOrder a p σ) :
    IsFeasible a (seqSchedule a σ) ∧
      ∀ S : Schedule m, IsFeasible a S →
        totalLoss p d (seqSchedule a σ) ≤ totalLoss p d S := by sorry

end McNaughtonSched.SingleProc

