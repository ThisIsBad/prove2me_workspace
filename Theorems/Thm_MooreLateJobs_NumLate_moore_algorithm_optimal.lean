import Mathlib
import Definitions.Def_MooreLateJobs_Shared_completionTime
import Definitions.Def_MooreLateJobs_NumLate_lateSet
import Definitions.Def_MooreLateJobs_NumLate_IsOptimal
import Definitions.Def_MooreLateJobs_NumLate_MooreStep

namespace MooreLateJobs.NumLate

theorem moore_algorithm_optimal {ι : Type*} [DecidableEq ι] (J : Finset ι) (t D : ι → ℝ)
    (ht : ∀ i ∈ J, 0 ≤ t i) (htD : ∀ i ∈ J, t i ≤ D i)
    (l₀ : List ι) (hl₀ : Shared.IsSchedule J l₀) (hspt : l₀.Pairwise (fun a b => t a ≤ t b))
    (cur rej : List ι) (hrun : Relation.ReflTransGen (MooreStep t D) (l₀, []) (cur, rej))
    (hterm : lateSet t D cur = ∅)
    (cur' : List ι) (hcur' : cur'.Perm cur) (hdd : cur'.Pairwise (fun a b => D a ≤ D b))
    (rej' : List ι) (hrej' : rej'.Perm rej) :
    IsOptimal t D J (cur' ++ rej') := by sorry

end MooreLateJobs.NumLate

