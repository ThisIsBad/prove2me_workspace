import Mathlib
import Definitions.Def_BurnInBatch_ListSched_Model

namespace BurnInBatch.ListSched

/-- Proof of Proposition 4, p. 773: the lateness optimum on a sub-instance
is at least its makespan optimum minus the full instance's largest due date. -/
theorem lateness_lower_bound {n : ℕ} (p d : Fin n → ℝ) (B m : ℕ)
    (J : Finset (Fin n)) (hn : 0 < n) (hJ : J.Nonempty)
    (hB : 0 < B) (hm : 0 < m) (hp : ∀ j, 0 < p j) :
    CmaxStar p B m J - maxDue d hn ≤ LStar p d B m J := by sorry

end BurnInBatch.ListSched

