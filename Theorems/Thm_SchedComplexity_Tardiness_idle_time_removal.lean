import Mathlib
import Definitions.Def_SchedComplexity_Tardiness_Model

namespace SchedComplexity.Tardiness

/-- Idle-time removal (proof of Theorem 4(d), p. 20): for a single-machine instance with
processing times `p`, weights `w` and due dates `d`, the schedule without idle time of every
processing order is feasible, and every feasible schedule `S` is improved (not worsened) in
`Σ w_j T_j` by the schedule without idle time of some processing order. -/
theorem idle_time_removal {n : ℕ} (p w d : Fin n → ℕ) :
    (∀ π : Equiv.Perm (Fin n), IsFeasible p (noIdleStart p π)) ∧
    ∀ S : Fin n → ℕ, IsFeasible p S →
      ∃ π : Equiv.Perm (Fin n), orderTWT p w d π ≤ totalWeightedTardiness p w d S := by sorry

end SchedComplexity.Tardiness

