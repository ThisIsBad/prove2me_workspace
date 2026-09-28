import Mathlib
import Definitions.Def_McNaughtonSched_SingleProc_Model

namespace McNaughtonSched.SingleProc

theorem exists_optimal_noSplit {m : ℕ} (a p d : Fin m → ℝ)
    (ha : ∀ i, 0 < a i) (hp : ∀ i, 0 ≤ p i) :
    ∃ S₀ : Schedule m, IsFeasible a S₀ ∧ NoSplit S₀ ∧
      ∀ S : Schedule m, IsFeasible a S → totalLoss p d S₀ ≤ totalLoss p d S := by sorry

end McNaughtonSched.SingleProc

