import Mathlib
import Definitions.Def_DeterioratingJobs_Weighted_Model

namespace DeterioratingJobs.Weighted

/-- Equation (2), p. 496, relabelled along an arbitrary schedule. -/
theorem eq2_completion_closed_form {Ω : Type*} {N : ℕ}
    (X : Fin N → Ω → ℝ) (α : Fin N → ℝ) (π : Equiv.Perm (Fin N))
    (k : ℕ) (hk : k ≤ N) (ω : Ω) :
    DeterioratingJobs.Makespan.completionTime X α π k ω =
      ∑ i : Fin N with i.val < k,
        X (π i) ω * ∏ r : Fin N with i < r ∧ r.val < k, (1 + α (π r)) := by sorry

end DeterioratingJobs.Weighted

