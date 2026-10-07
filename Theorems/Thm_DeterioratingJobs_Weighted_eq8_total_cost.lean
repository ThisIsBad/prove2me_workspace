import Mathlib
import Definitions.Def_DeterioratingJobs_Weighted_Model

namespace DeterioratingJobs.Weighted

/-- Equation (8), p. 497, relabelled along an arbitrary schedule. -/
theorem eq8_total_cost {Ω : Type*} {N : ℕ}
    (X : Fin N → Ω → ℝ) (α c : Fin N → ℝ)
    (π : Equiv.Perm (Fin N)) (ω : Ω) :
    totalCost X α c π ω =
      ∑ k : Fin N, c (π k) *
        ∑ i : Fin N with i ≤ k,
          X (π i) ω * ∏ r : Fin N with i < r ∧ r ≤ k, (1 + α (π r)) := by sorry

end DeterioratingJobs.Weighted

