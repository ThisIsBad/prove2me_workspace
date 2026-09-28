import Mathlib

namespace MooreLateJobs.Shared

/-- A schedule of the job set `J` (Moore 1968, p. 104): a specific ordering of the jobs of `J`,
encoded as a duplicate-free list whose elements are exactly the jobs of `J`. -/
def IsSchedule {ι : Type*} (J : Finset ι) (l : List ι) : Prop :=
  l.Nodup ∧ ∀ x, x ∈ l ↔ x ∈ J

/-- Completion time of the job in (0-based) position `k` of the sequence `l`: the machine starts
at time `0` and processes the jobs one after another without idle time or interruption (p. 102),
so the `k`-th job completes at the sum of the processing times of the first `k + 1` jobs. -/
def completionAt {ι : Type*} (t : ι → ℝ) (l : List ι) (k : ℕ) : ℝ :=
  ((l.take (k + 1)).map t).sum

/-- Completion time `C_j` of job `j` in the sequence `l` (the completion time at the position of
its first occurrence; sequences in this development are duplicate-free). -/
def completionTime {ι : Type*} [DecidableEq ι] (t : ι → ℝ) (l : List ι) (j : ι) : ℝ :=
  completionAt t l (l.idxOf j)

end MooreLateJobs.Shared
