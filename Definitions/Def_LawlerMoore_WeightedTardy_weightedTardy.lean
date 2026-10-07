import Mathlib
import Definitions.Def_MooreLateJobs_Shared_completionTime
import Definitions.Def_MooreLateJobs_NumLate_lateSet

namespace LawlerMoore.WeightedTardy

/-- The total loss of §5 (Lawler–Moore 1969, p. 79): the weighted number of tardy jobs of the
sequence `l` of the jobs `Fin n` (Lean job `j` is the paper's job `j + 1`). Job `j` has the
integer processing time `a' j` and the integer deadline `d j`; it incurs the loss
`c_j(t) = 0` for `t ≤ d_j` and `c_j(t) = p_j` for `t > d_j`, where `t` is its completion time
when the jobs of `l` are processed one immediately following the other from time `0`. So the
total loss is the sum of `p j` over the jobs of `l` with `d j < C_j`, i.e. over the late set. -/
noncomputable def weightedTardy {n : ℕ} (a' d : Fin n → ℕ) (p : Fin n → ℝ)
    (l : List (Fin n)) : ℝ :=
  ∑ j ∈ MooreLateJobs.NumLate.lateSet (fun j => (a' j : ℝ)) (fun j => (d j : ℝ)) l, p j

end LawlerMoore.WeightedTardy
