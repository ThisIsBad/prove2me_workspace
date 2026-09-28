import Mathlib
import Definitions.Def_MooreLateJobs_NumLate_lateSet

namespace MooreLateJobs.NumLate

/-- The ordered set `A` of a schedule `S` (p. 105): the early jobs of `S` (the set `E`) in their
order in `S`. -/
noncomputable def earlyPart {ι : Type*} [DecidableEq ι] (t D : ι → ℝ) (S : List ι) : List ι :=
  S.filter (fun j => j ∉ lateSet t D S)

/-- The ordered set `R` of a schedule `S` (p. 105): the late jobs of `S` (the set `L`) in their
order in `S`. -/
noncomputable def latePart {ι : Type*} [DecidableEq ι] (t D : ι → ℝ) (S : List ι) : List ι :=
  S.filter (fun j => j ∈ lateSet t D S)

end MooreLateJobs.NumLate
