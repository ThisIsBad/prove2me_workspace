import Mathlib
import Definitions.Def_DeterioratingJobs_Makespan_Model

namespace DeterioratingJobs.Makespan

/-- Eq. (2) (Browne–Yechiali 1990, p. 496), along an arbitrary schedule `π`: for every `k ≤ N`,
`S_k(π) = ∑_{i < k} X_{π(i)} ∏_{i < r < k} (1 + α_{π(r)})` (positions 0-based; empty product `= 1`). -/
theorem eq2_completion_closed_form {Ω : Type*} {N : ℕ} (X : Fin N → Ω → ℝ) (α : Fin N → ℝ)
    (π : Equiv.Perm (Fin N)) (k : ℕ) (hk : k ≤ N) (ω : Ω) :
    completionTime X α π k ω =
      ∑ i ∈ Finset.univ.filter (fun i : Fin N => i.val < k),
        X (π i) ω * ∏ r ∈ Finset.univ.filter (fun r : Fin N => i < r ∧ r.val < k),
          (1 + α (π r)) := by sorry

end DeterioratingJobs.Makespan

