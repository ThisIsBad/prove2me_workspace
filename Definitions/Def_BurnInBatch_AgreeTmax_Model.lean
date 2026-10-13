import Mathlib

namespace BurnInBatch.AgreeTmax

/-! The single batch processing machine of Lee, Uzsoy & Martin-Vega, *Efficient Algorithms for
Scheduling Semiconductor Burn-In Operations*, Oper. Res. 40(4) (1992), §2 (p. 766), Definition 1
(p. 767), specialised to §3's problem `1/B/T_max` in which all jobs are available at time 0
(p. 769).

Jobs are `Fin n` (the paper's job `i` is `i - 1`). Each job `i` has a processing time `p i` and a
due date `d i` (natural numbers: the paper assumes all data integral, p. 769). A batch schedule is
a list of batches (finite sets of jobs) in processing order. A batch takes the processing time of
its longest job; batches are processed back to back from time 0 (no inserted idle time, which
cannot help any regular objective; with no release times this is the paper's convention). -/

/-- The jobs `1, …, j` of the paper, i.e. the jobs with 0-based index `< j`. -/
def jobsUpTo (n j : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i => i.val < j

/-- A valid batch schedule of the job set `J` on a machine of capacity `B` (Assumption 2):
every batch is nonempty, has at most `B` jobs and consists of jobs of `J`; the batches are
pairwise disjoint; every job of `J` lies in some batch. -/
def IsValid {n : ℕ} (B : ℕ) (J : Finset (Fin n)) (S : List (Finset (Fin n))) : Prop :=
  (∀ P ∈ S, P.Nonempty) ∧ (∀ P ∈ S, P.card ≤ B) ∧ (∀ P ∈ S, P ⊆ J) ∧
    S.Pairwise Disjoint ∧ ∀ i ∈ J, ∃ P ∈ S, i ∈ P

/-- Processing time of a batch: the processing time of its longest job (Assumption 3). -/
def batchTime {n : ℕ} (p : Fin n → ℕ) (P : Finset (Fin n)) : ℕ :=
  P.sup p

/-- Completion time of the batch at position `k` (0-based) of `S`: the batches `0, …, k` run back
to back from time 0. -/
def batchCompletion {n : ℕ} (p : Fin n → ℕ) (S : List (Finset (Fin n))) (k : ℕ) : ℕ :=
  ((S.take (k + 1)).map (batchTime p)).sum

/-- Makespan `C_max`: completion time of the last batch (0 for the empty schedule). -/
def makespan {n : ℕ} (p : Fin n → ℕ) (S : List (Finset (Fin n))) : ℕ :=
  (S.map (batchTime p)).sum

/-- Maximum tardiness `T_max = max_i max(0, C_i - d_i)`, where a job's completion time `C_i` is
the completion time of its batch (truncated subtraction in `ℕ` is `max(0, ·)`); `0` for the empty
schedule. -/
def Tmax {n : ℕ} (p d : Fin n → ℕ) (S : List (Finset (Fin n))) : ℕ :=
  Finset.univ.sup fun k : Fin S.length => (S.get k).sup fun i => batchCompletion p S k.val - d i

/-- Definition 1 (p. 767): the sequence is in batch-EDD order if for any two batches `P`, `Q`
with `P` processed before `Q` there is no pair of jobs `i ∈ P`, `j ∈ Q` with `d i > d j`. -/
def IsBatchEDD {n : ℕ} (d : Fin n → ℕ) (S : List (Finset (Fin n))) : Prop :=
  ∀ a b : Fin S.length, a < b → ∀ i ∈ S.get a, ∀ j ∈ S.get b, ¬ d j < d i

/-- Processing times and due dates are agreeable (p. 769), in the strict form:
`p i < p j` implies `d i ≤ d j`. -/
def Agreeable {n : ℕ} (p d : Fin n → ℕ) : Prop :=
  ∀ i j : Fin n, p i < p j → d i ≤ d j

/-- The batches are sets of consecutively indexed jobs, and the batches appear in increasing
order of job index: a consecutive partition (p. 768). -/
def IsConsecutive {n : ℕ} (S : List (Finset (Fin n))) : Prop :=
  (∀ P ∈ S, ∀ i j k : Fin n, i ∈ P → k ∈ P → i ≤ j → j ≤ k → j ∈ P) ∧
    ∀ a b : Fin S.length, a < b → ∀ i ∈ S.get a, ∀ j ∈ S.get b, i < j

end BurnInBatch.AgreeTmax
