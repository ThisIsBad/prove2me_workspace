import Mathlib
import Definitions.Def_NumStochOpt_ListScheduling_ListSchedule
import Definitions.Def_NumStochOpt_ListScheduling_Makespan
import Definitions.Def_BurnInBatch_ListSched_Model

namespace BurnInBatch.BatchLPT

open NumStochOpt.ListScheduling

/-- A valid batching of the jobs `0, …, n-1` into batches of at most `B` jobs (Assumption 2,
p. 766): every batch is nonempty and holds at most `B` jobs, distinct batches are disjoint,
and every job lies in some batch. The list order is the order in which the batches are
listed; it carries no meaning for the makespan. -/
def IsBatching (n B : ℕ) (S : List (Finset (Fin n))) : Prop :=
  (∀ P ∈ S, P.Nonempty ∧ P.card ≤ B) ∧ S.Pairwise Disjoint ∧ ∀ j : Fin n, ∃ P ∈ S, j ∈ P

/-- `C*`, the optimal makespan of `P/B/C_max` (§5, p. 771): the minimum, over all valid
batchings `S` (any batch sizes `≤ B`, any grouping of jobs) and all assignments of the
batches to the `m` identical machines, of the largest machine load, where a batch occupies
its machine for its batch time. All jobs are available at time `0`. -/
noncomputable def optBatchMakespan (n m B : ℕ) (p : Fin n → ℝ) : ℝ :=
  ⨅ S : {S : List (Finset (Fin n)) // IsBatching n B S},
    optMakespan S.1.length m (BurnInBatch.ListSched.batchTimes p S.1)

/-- Completion time of batch `k` when the batches of `S` (with item times `q`) are assigned
to machines by `σ` and each machine processes its batches back to back from time `0` in list
order: the total time of the batches `k' ≤ k` on the machine of `k`. -/
def batchCompletion {M m : ℕ} (q : ℕ → ℝ) (σ : Fin M → Fin m) (k : Fin M) : ℝ :=
  ∑ k' : Fin M, if k' ≤ k ∧ σ k' = σ k then q (k' : ℕ) else 0

/-- Completion time of job `j` given the completion times `c` of the batches of `S`: the
completion time of the batch containing `j` (in a valid batching that batch is unique). -/
def jobCompletion {n : ℕ} (S : List (Finset (Fin n))) (c : Fin S.length → ℝ) (j : Fin n) : ℝ :=
  ∑ k : Fin S.length, if j ∈ S.get k then c k else 0

/-- The maximum lateness `L_max = max_j (C_j - d_j)` of the parallel batch schedule given
by the batching `S` and the assignment `σ` (each machine in list order, no idle time). -/
noncomputable def scheduleLmax {n m : ℕ} (p d : Fin n → ℝ) (S : List (Finset (Fin n)))
    (σ : Fin S.length → Fin m) : ℝ :=
  ⨆ j : Fin n, (jobCompletion S (batchCompletion (BurnInBatch.ListSched.batchTimes p S) σ) j - d j)

/-- `L*`, the optimal maximum lateness of `P/B/L_max` (p. 773): the minimum of
`scheduleLmax` over all valid batchings and all assignments. Every processing order on a
machine is represented by a reordering of `S`. -/
noncomputable def optLmax (n m B : ℕ) (p d : Fin n → ℝ) : ℝ :=
  ⨅ S : {S : List (Finset (Fin n)) // IsBatching n B S},
    ⨅ σ : Fin S.1.length → Fin m, scheduleLmax p d S.1 σ

/-- `d_max`, the largest due date. -/
noncomputable def dMax {n : ℕ} (d : Fin n → ℝ) : ℝ := ⨆ j : Fin n, d j

end BurnInBatch.BatchLPT
