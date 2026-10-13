import Mathlib
import Definitions.Def_BurnInBatch_ListSched_Model

namespace BurnInBatch.ListSched

/-- Proposition 1, p. 772, also valid for every sub-instance `J`. -/
theorem proposition_1 {n : ℕ} (p : Fin n → ℝ) (B m : ℕ)
    (J : Finset (Fin n)) (l : List (Fin n))
    (hB : 0 < B) (hm : 0 < m) (hp : ∀ j, 0 < p j)
    (hl : ListsJobs J l) :
    blsMakespan p B m l ≤
      ((B : ℝ) + 1 - 1 / (m : ℝ)) * CmaxStar p B m J := by sorry

end BurnInBatch.ListSched

