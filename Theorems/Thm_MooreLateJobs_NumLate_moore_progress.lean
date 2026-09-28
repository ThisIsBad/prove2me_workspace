import Mathlib
import Definitions.Def_MooreLateJobs_Shared_completionTime
import Definitions.Def_MooreLateJobs_NumLate_lateSet
import Definitions.Def_MooreLateJobs_NumLate_MooreStep

namespace MooreLateJobs.NumLate

theorem moore_progress {ι : Type*} [DecidableEq ι] (J : Finset ι) (t D : ι → ℝ)
    (ht : ∀ i ∈ J, 0 ≤ t i) (htD : ∀ i ∈ J, t i ≤ D i)
    (l₀ : List ι) (hl₀ : Shared.IsSchedule J l₀) (hspt : l₀.Pairwise (fun a b => t a ≤ t b))
    (cur rej : List ι) (hrun : Relation.ReflTransGen (MooreStep t D) (l₀, []) (cur, rej))
    (hlate : (lateSet t D cur).Nonempty) :
    ∃ s' : List ι × List ι, MooreStep t D (cur, rej) s' := by sorry

end MooreLateJobs.NumLate

