import Mathlib
import Definitions.Def_MooreLateJobs_Shared_completionTime

namespace EmmonsTardiness.SPT

open MooreLateJobs

/-- Tardiness `T_i = max(0, C_i − d_i)` of job `i` in the sequence `l` (Emmons 1969, p. 701):
`C_i = Shared.completionTime p l i` is the completion time of `i` when the jobs of `l` are
processed in order from time `0` without idle time, `p` being the processing times and `d` the
due dates. -/
noncomputable def tardiness {ι : Type*} [DecidableEq ι] (p d : ι → ℝ) (l : List ι) (i : ι) : ℝ :=
  max 0 (Shared.completionTime p l i - d i)

/-- Total tardiness `T = Σ_{i ∈ J} T_i` of the sequence `l` over the job set `J` (p. 701). -/
noncomputable def totalTardiness {ι : Type*} [DecidableEq ι] (p d : ι → ℝ) (J : Finset ι)
    (l : List ι) : ℝ :=
  ∑ i ∈ J, tardiness p d l i

/-- `l` is an optimal schedule of `J`: it is a schedule of `J` (a duplicate-free list whose
elements are exactly the jobs of `J`) and its total tardiness is at most that of every schedule
of `J`. -/
def IsOptimal {ι : Type*} [DecidableEq ι] (p d : ι → ℝ) (J : Finset ι) (l : List ι) : Prop :=
  Shared.IsSchedule J l ∧
    ∀ l' : List ι, Shared.IsSchedule J l' → totalTardiness p d J l ≤ totalTardiness p d J l'

/-- Job `a` precedes job `b` in the sequence `l`: `a` occurs at an earlier position than `b`. -/
def Precedes {ι : Type*} [DecidableEq ι] (l : List ι) (a b : ι) : Prop :=
  l.idxOf a < l.idxOf b

/-- The indexing convention of p. 703: jobs are indexed (by the linear order of `ι`) in order of
nondecreasing processing times and, in case of equality, of nondecreasing due dates, i.e.
`j < k` implies `p_j < p_k`, or `p_j = p_k` and `d_j ≤ d_k`. -/
def IsSPTIndexed {ι : Type*} [LinearOrder ι] (p d : ι → ℝ) (J : Finset ι) : Prop :=
  ∀ i ∈ J, ∀ k ∈ J, i < k → p i < p k ∨ (p i = p k ∧ d i ≤ d k)

/-- The SPT schedule: the jobs of `J` in increasing index order. Under `IsSPTIndexed p d J` this
is shortest-processing-time order with ties broken by earliest due date. -/
def sptSchedule {ι : Type*} [LinearOrder ι] (J : Finset ι) : List ι :=
  J.sort (· ≤ ·)

end EmmonsTardiness.SPT
