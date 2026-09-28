import Mathlib
import Definitions.Def_MooreLateJobs_Shared_completionTime

namespace MooreLateJobs.NumLate

/-- The set `L` of late jobs of the sequence `l` (p. 105): `J_j ∈ L` iff `C_j > D_j`.
The early set `E` (`C_j ≤ D_j`) is the complement of `L` among the jobs of `l`. -/
noncomputable def lateSet {ι : Type*} [DecidableEq ι] (t D : ι → ℝ) (l : List ι) : Finset ι :=
  l.toFinset.filter (fun j => D j < Shared.completionTime t l j)

end MooreLateJobs.NumLate
