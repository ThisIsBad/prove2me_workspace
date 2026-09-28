import Mathlib
import Definitions.Def_MooreLateJobs_Shared_completionTime
import Definitions.Def_MooreLateJobs_NumLate_lateSet
import Definitions.Def_MooreLateJobs_NumLate_IsOptimal

namespace MooreLateJobs.NumLate

theorem repeated_elimination_optimal {ι : Type*} [DecidableEq ι] (J : Finset ι) (t D : ι → ℝ)
    (ht : ∀ i ∈ J, 0 ≤ t i) (htD : ∀ i ∈ J, t i ≤ D i)
    (rej : List ι) (hnd : rej.Nodup) (hsub : ∀ j ∈ rej, j ∈ J)
    (hfound : ∀ (k : ℕ) (hk : k < rej.length), ∃ S : List ι,
      IsOptimal t D (J \ (rej.take k).toFinset) S ∧ rej[k] ∈ lateSet t D S)
    (hfeas : ∃ S : List ι, Shared.IsSchedule (J \ rej.toFinset) S ∧ lateSet t D S = ∅)
    (AD : List ι) (hAD : Shared.IsSchedule (J \ rej.toFinset) AD)
    (hdd : AD.Pairwise (fun a b => D a ≤ D b))
    (P : List ι) (hP : P.Perm rej) :
    IsOptimal t D J (AD ++ P) := by sorry

end MooreLateJobs.NumLate

