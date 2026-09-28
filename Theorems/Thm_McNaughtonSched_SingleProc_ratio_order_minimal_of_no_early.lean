import Mathlib
import Definitions.Def_McNaughtonSched_SingleProc_Model

namespace McNaughtonSched.SingleProc

theorem ratio_order_minimal_of_no_early {m : ℕ} (a p d : Fin m → ℝ)
    (ha : ∀ i, 0 < a i) (hp : ∀ i, 0 ≤ p i)
    (σ : Equiv.Perm (Fin m)) (hσ : InRatioOrder a p σ)
    (hlate : ∀ i, d i ≤ completion (seqSchedule a σ) i) :
    IsFeasible a (seqSchedule a σ) ∧
      ∀ S : Schedule m, IsFeasible a S →
        totalLoss p d (seqSchedule a σ) ≤ totalLoss p d S := by sorry

end McNaughtonSched.SingleProc

