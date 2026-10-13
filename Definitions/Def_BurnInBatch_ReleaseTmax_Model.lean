import Mathlib

namespace BurnInBatch.ReleaseTmax

/-- The first `j` jobs of the index order: the 0-based jobs `0, …, j - 1`, i.e. the paper's
jobs `1, …, j`. -/
def prefixJobs (n j : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i : Fin n => i.val < j)

/-- A batch schedule of the job set `J` on one batch machine of capacity `B`: a list of batches
in processing order, each nonempty with at most `B` jobs, pairwise disjoint, whose union is `J`. -/
def IsBatchSchedule {n : ℕ} (B : ℕ) (J : Finset (Fin n)) (S : List (Finset (Fin n))) : Prop :=
  (∀ P ∈ S, P.Nonempty ∧ P.card ≤ B) ∧
  S.Pairwise (fun P Q => Disjoint P Q) ∧
  ∀ j : Fin n, j ∈ J ↔ ∃ P ∈ S, j ∈ P

/-- The release time `r(P) = max {r_k | k ∈ P}` of a batch (for a nonempty batch). -/
def batchRelease {n : ℕ} (r : Fin n → ℕ) (P : Finset (Fin n)) : ℕ :=
  P.sup r

/-- Completion time of the last batch when the batches `S` are processed in order, each of
duration `p`, the previous batch having completed at time `t`: a batch starts at
`max (previous completion, r(P))` and completes `p` later. -/
def finish {n : ℕ} (p : ℕ) (r : Fin n → ℕ) : List (Finset (Fin n)) → ℕ → ℕ
  | [], t => t
  | P :: S, t => finish p r S (max t (batchRelease r P) + p)

/-- The makespan of the batch schedule `S`: the completion time of its last batch, starting from
time `0` (it is `0` for the empty schedule). -/
def makespan {n : ℕ} (p : ℕ) (r : Fin n → ℕ) (S : List (Finset (Fin n))) : ℕ :=
  finish p r S 0

/-- Auxiliary recursion for `jobCompletion`: `t` is the completion time of the previous batch. -/
def jobCompletionAux {n : ℕ} (p : ℕ) (r : Fin n → ℕ) (j : Fin n) :
    List (Finset (Fin n)) → ℕ → ℕ
  | [], _ => 0
  | P :: S, t =>
      if j ∈ P then max t (batchRelease r P) + p
      else jobCompletionAux p r j S (max t (batchRelease r P) + p)

/-- The completion time `C_j` of job `j` in the batch schedule `S`: the completion time of the
batch containing `j` (only used for jobs that lie in some batch). -/
def jobCompletion {n : ℕ} (p : ℕ) (r : Fin n → ℕ) (S : List (Finset (Fin n))) (j : Fin n) : ℕ :=
  jobCompletionAux p r j S 0

/-- Every job of `J` is on time in `S`: `C_j ≤ d_j`. For a batch schedule of `J` this is the
paper's "schedule with `T_max = 0`" (a feasible schedule). -/
def AllOnTime {n : ℕ} (p : ℕ) (r d : Fin n → ℕ) (J : Finset (Fin n))
    (S : List (Finset (Fin n))) : Prop :=
  ∀ j ∈ J, jobCompletion p r S j ≤ d j

/-- Maximum tardiness `T_max = max_{j ∈ J} max(0, C_j − d_j)` of `S` over the jobs of `J`
(natural-number subtraction truncates at `0`, so `C_j - d_j` is `max(0, C_j − d_j)`; the
maximum over an empty `J` is `0`). -/
def tmax {n : ℕ} (p : ℕ) (r d : Fin n → ℕ) (J : Finset (Fin n))
    (S : List (Finset (Fin n))) : ℕ :=
  J.sup (fun j => jobCompletion p r S j - d j)

/-- Definition 1 (batch-EDD order): for any two batches `P` before `Q` in `S` there are no jobs
`i ∈ P`, `j ∈ Q` with `d_i > d_j`. -/
def IsBatchEDD {n : ℕ} (d : Fin n → ℕ) (S : List (Finset (Fin n))) : Prop :=
  S.Pairwise (fun P Q => ∀ i ∈ P, ∀ j ∈ Q, d i ≤ d j)

/-- Every batch of `S` is a set of consecutively indexed jobs `{a, a + 1, …, b - 1}` (0-based),
and the batches appear in increasing index order: every job of an earlier batch has a smaller
index than every job of a later batch. -/
def IsConsecutive {n : ℕ} (S : List (Finset (Fin n))) : Prop :=
  (∀ P ∈ S, ∃ a b : ℕ, P = Finset.univ.filter (fun i : Fin n => a ≤ i.val ∧ i.val < b)) ∧
  S.Pairwise (fun P Q => ∀ i ∈ P, ∀ j ∈ Q, i < j)

end BurnInBatch.ReleaseTmax
