import Mathlib
import Definitions.Def_MooreLateJobs_Shared_completionTime
import Definitions.Def_MooreLateJobs_NumLate_lateSet

namespace MooreLateJobs.NumLate

/-- `l` is an optimal schedule for the job set `J`: it is a schedule of `J`, and no schedule of
`J` has fewer late jobs (the objective of p. 102, "minimize the number of late jobs"). -/
def IsOptimal {ι : Type*} [DecidableEq ι] (t D : ι → ℝ) (J : Finset ι) (l : List ι) : Prop :=
  Shared.IsSchedule J l ∧ ∀ l' : List ι, Shared.IsSchedule J l' → (lateSet t D l).card ≤ (lateSet t D l').card

end MooreLateJobs.NumLate
