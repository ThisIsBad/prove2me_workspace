import Mathlib
import Definitions.Def_McNaughtonSched_SingleProc_Model

namespace McNaughtonSched.SingleProc

theorem split_reduction {m : ℕ} (a p d : Fin m → ℝ)
    (ha : ∀ i, 0 < a i) (hp : ∀ i, 0 ≤ p i)
    (S : Schedule m) (hS : IsFeasible a S) (hsplit : m < S.length) :
    ∃ S' : Schedule m, IsFeasible a S' ∧ S'.length < S.length ∧
      totalLoss p d S' ≤ totalLoss p d S := by sorry

end McNaughtonSched.SingleProc

