import Mathlib
import Definitions.Def_MooreLateJobs_Shared_completionTime
import Definitions.Def_EmmonsTardiness_SPT_Model

namespace EmmonsTardiness.SPT

open MooreLateJobs

/-- Emmons 1969, Corollary 1.4, p. 705: the SPT schedule is optimal if
`d_j + p_j ≤ Σ_{i=1}^{j+1} p_i` for `j = 1, …, n − 1`.

Index translation: `L = sptSchedule J` lists the jobs `J_1, …, J_n` in index order, so the
paper's 1-based job `J_j` is the 0-based entry `L[m]` with `m = j − 1`; the right-hand side
`Σ_{i=1}^{j+1} p_i` is the SPT completion time of `J_{j+1}`, i.e. `completionAt p L (m + 1)` (the
sum of the first `m + 2 = j + 1` processing times); and the range `j = 1, …, n − 1` is
`m + 1 < L.length`. Processing times are assumed nonnegative (added, disclosed). The reduction
`d_i < Σ_J p` of p. 703 is not imposed. -/
theorem corollary_1_4 {ι : Type*} [LinearOrder ι] (p d : ι → ℝ) (J : Finset ι)
    (hp : ∀ i ∈ J, 0 ≤ p i) (hidx : IsSPTIndexed p d J)
    (hcond : ∀ (m : ℕ) (hm : m + 1 < (sptSchedule J).length),
      d ((sptSchedule J)[m]'(by omega)) + p ((sptSchedule J)[m]'(by omega)) ≤
        Shared.completionAt p (sptSchedule J) (m + 1)) :
    IsOptimal p d J (sptSchedule J) := by sorry

end EmmonsTardiness.SPT

