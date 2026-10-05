import Mathlib
import Definitions.Def_MooreLateJobs_Shared_completionTime
import Definitions.Def_EmmonsTardiness_SPT_Model

namespace EmmonsTardiness.SPT

open MooreLateJobs

/-- Emmons 1969, proof of Theorem 1, p. 703, first paragraph: in a schedule satisfying
hypothesis (1) (every job of `B` precedes `k`) in which `k` precedes `j`, interchanging `j` and
`k` does not increase total tardiness, provided `j < k` in the SPT indexing and hypothesis (2)
`d_j ≤ max(Σ_{i∈B} p_i + p_k, d_k)` holds. The interchanged sequence `l.map (Equiv.swap j k)` is
again a schedule of `J`, with `j` before `k` and every job of `B` still before `k`; these
companion facts are stated as the first three conjuncts. Processing times are assumed
nonnegative (an added, disclosed hypothesis: they are durations). -/
theorem interchange_le {ι : Type*} [LinearOrder ι] (p d : ι → ℝ) (J : Finset ι)
    (hp : ∀ i ∈ J, 0 ≤ p i) (hidx : IsSPTIndexed p d J)
    (j k : ι) (hj : j ∈ J) (hk : k ∈ J) (hjk : j < k)
    (B : Finset ι) (hB : B ⊆ J)
    (h2 : d j ≤ max ((∑ i ∈ B, p i) + p k) (d k))
    (l : List ι) (hl : Shared.IsSchedule J l)
    (hBl : ∀ i ∈ B, Precedes l i k) (hkj : Precedes l k j) :
    Shared.IsSchedule J (l.map (Equiv.swap j k)) ∧
      (∀ i ∈ B, Precedes (l.map (Equiv.swap j k)) i k) ∧
      Precedes (l.map (Equiv.swap j k)) j k ∧
      totalTardiness p d J (l.map (Equiv.swap j k)) ≤ totalTardiness p d J l := by sorry

end EmmonsTardiness.SPT

