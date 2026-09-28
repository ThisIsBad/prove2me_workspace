import Mathlib
import Definitions.Def_MooreLateJobs_Shared_completionTime
import Definitions.Def_MooreLateJobs_NumLate_lateSet
import Definitions.Def_MooreLateJobs_NumLate_IsOptimal
import Definitions.Def_MooreLateJobs_NumLate_earlyPart

namespace MooreLateJobs.NumLate

theorem lemma3 {ι : Type*} [DecidableEq ι] (J : Finset ι) (t D : ι → ℝ)
    (ht : ∀ i ∈ J, 0 ≤ t i) (htD : ∀ i ∈ J, t i ≤ D i)
    (S : List ι) (hS : IsOptimal t D J S) (hL : (lateSet t D S).Nonempty)
    (Jstar : Finset ι) (hJstar : Jstar ⊆ lateSet t D S)
    (S' : List ι) (hS' : IsOptimal t D (J \ Jstar) S')
    (hform : S' = earlyPart t D S' ++ latePart t D S')
    (P'' : List ι) (hP'' : Shared.IsSchedule (Jstar ∪ lateSet t D S') P'') :
    IsOptimal t D J (earlyPart t D S' ++ P'') ∧
      lateSet t D (earlyPart t D S' ++ P'') = Jstar ∪ lateSet t D S' := by sorry

end MooreLateJobs.NumLate

