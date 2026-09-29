import Mathlib
import Definitions.Def_AvgCompletionSched_DelayList_Model

namespace AvgCompletionSched.DelayList

/-- Lemma 4.10 (p. 160): `C^m_opt ≥ C^1_opt / m`. For every feasible `m`-machine schedule `N`
there is a feasible one-machine schedule of the same instance (same release dates and precedence
constraints) whose sum of weighted completion times is at most `m` times that of `N`. -/
theorem one_machine_lower_bound {n m : ℕ} (I : Instance n) (N : Schedule I m) :
    ∃ S1 : Schedule I 1, S1.wct ≤ (m : ℝ) * N.wct := by sorry

end AvgCompletionSched.DelayList
