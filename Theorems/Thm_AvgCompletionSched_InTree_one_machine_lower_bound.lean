import Mathlib
import Definitions.Def_AvgCompletionSched_InTree_Model

namespace AvgCompletionSched.InTree

/-- Lemma 4.10 (p. 160): `C^m_opt ≥ C^1_opt / m`. -/
theorem one_machine_lower_bound {n : ℕ} (I : Instance n) (m : ℕ) (hm : 1 ≤ m)
    (π : Fin n ≃ Fin n) (hπ : IsOptimalOneMachine I π) (N : Schedule I m) :
    oneMachineWct I π / (m : ℝ) ≤ N.wct := by sorry

end AvgCompletionSched.InTree

