import Mathlib
import Definitions.Def_MooreLateJobs_NumLate_lateSet
import Definitions.Def_MooreLateJobs_NumLate_IsOptimal
import Definitions.Def_MooreLateJobs_NumLate_earlyPart

namespace MooreLateJobs.NumLate

theorem lemma1 {ι : Type*} [DecidableEq ι] (J : Finset ι) (t D : ι → ℝ)
    (ht : ∀ i ∈ J, 0 ≤ t i) (htD : ∀ i ∈ J, t i ≤ D i)
    (S : List ι) (hS : IsOptimal t D J S) :
    (lateSet t D (earlyPart t D S ++ latePart t D S)).card = (lateSet t D S).card ∧
    ∀ P : List ι, P.Perm (latePart t D S) →
      (lateSet t D (earlyPart t D S ++ P)).card = (lateSet t D S).card := by sorry

end MooreLateJobs.NumLate

