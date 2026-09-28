import Mathlib
import Definitions.Def_MooreLateJobs_NumLate_lateSet
import Definitions.Def_MooreLateJobs_NumLate_IsOptimal

namespace MooreLateJobs.NumLate

theorem selection_case2 {ι : Type*} [DecidableEq ι] (Jc : Finset ι) (t D : ι → ℝ)
    (ht : ∀ i ∈ Jc, 0 ≤ t i) (htD : ∀ i ∈ Jc, t i ≤ D i)
    (pre : List ι) (q : ι) (hq : q ∈ Jc) (hqpre : q ∉ pre) (hpreJ : ∀ a ∈ pre, a ∈ Jc)
    (hnd : pre.Nodup) (hdd : pre.Pairwise (fun a b => D a ≤ D b))
    (hearly : lateSet t D pre = ∅)
    (htpre : ∀ a ∈ pre, t a ≤ t q) (htrest : ∀ b ∈ Jc, b ∉ pre → b ≠ q → t q ≤ t b)
    (k : ℕ) (hk₁ : ∀ a ∈ pre.take k, D a ≤ D q) (hk₂ : ∀ a ∈ pre.drop k, D q ≤ D a)
    (hlate : q ∈ lateSet t D (pre.take k ++ q :: pre.drop k)) :
    ∃ S : List ι, IsOptimal t D Jc S ∧ q ∈ lateSet t D S := by sorry

end MooreLateJobs.NumLate

