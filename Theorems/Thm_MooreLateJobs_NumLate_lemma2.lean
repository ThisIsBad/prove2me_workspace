import Mathlib
import Definitions.Def_MooreLateJobs_NumLate_lateSet
import Definitions.Def_MooreLateJobs_NumLate_IsOptimal
import Definitions.Def_MooreLateJobs_NumLate_earlyPart

namespace MooreLateJobs.NumLate

theorem lemma2 {ι : Type*} [DecidableEq ι] (J : Finset ι) (t D : ι → ℝ)
    (ht : ∀ i ∈ J, 0 ≤ t i) (htD : ∀ i ∈ J, t i ≤ D i)
    (S : List ι) (hS : IsOptimal t D J S) (hform : S = earlyPart t D S ++ latePart t D S)
    (AD : List ι) (hAD : AD.Perm (earlyPart t D S)) (hdd : AD.Pairwise (fun a b => D a ≤ D b)) :
    IsOptimal t D J (AD ++ latePart t D S) ∧
      lateSet t D (AD ++ latePart t D S) = lateSet t D S := by sorry

end MooreLateJobs.NumLate

