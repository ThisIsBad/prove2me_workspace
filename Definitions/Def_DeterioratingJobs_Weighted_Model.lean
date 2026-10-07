import Mathlib
import Definitions.Def_DeterioratingJobs_Makespan_Model

namespace DeterioratingJobs.Weighted

open MeasureTheory

/-- Sum of each job's waiting cost rate times its completion time (p. 497).
The job at zero-based position `k` is `π k` and finishes at `S_(k+1)`. -/
def totalCost {Ω : Type*} {N : ℕ} (X : Fin N → Ω → ℝ)
    (α c : Fin N → ℝ) (π : Equiv.Perm (Fin N)) (ω : Ω) : ℝ :=
  ∑ k : Fin N, c (π k) * DeterioratingJobs.Makespan.completionTime X α π (k.val + 1) ω

end DeterioratingJobs.Weighted
