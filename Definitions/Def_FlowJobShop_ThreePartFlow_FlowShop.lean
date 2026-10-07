import Mathlib

namespace FlowJobShop.ThreePartFlow

/-- A flow shop (Gonzalez–Sahni 1978, p. 36): `m ≥ 1` processors `P_1, …, P_m`, indexed by
`Fin m` (`P_1 = 0`, `P_m = m - 1`), and a set of jobs indexed by a type `J`. Task `j` of job `i`
must be performed on processor `P_j` and takes time `t j i = t_{j,i} ≥ 0`. Zero task times are
allowed. -/
structure FlowShop (m : ℕ) (J : Type*) where
  /-- The paper's flow shop has at least one processor. -/
  m_pos : 1 ≤ m
  /-- processing time `t_{j,i}` of task `j` of job `i` -/
  t : Fin m → J → ℝ
  t_nonneg : ∀ j i, 0 ≤ t j i

namespace FlowShop

variable {m : ℕ} {J : Type*}

/-- A **preemptive schedule** of a flow shop, in the paper's own representation (footnote 1,
p. 40: "the triple `(l_i, s_i, f_i)` means task `l_i` is processed on processor `j` from `s_i`
to `f_i`"). `pieces j i` is the finite set of pieces `(s, f)` of task `j` of job `i`, each
meaning that this task is processed on `P_j` during `[s, f)`. The conditions are:
* every piece satisfies `0 ≤ s < f` (the schedule starts at time zero);
* two different pieces on the same processor are disjoint as half-open intervals;
* the pieces of a task have total length equal to the task time (so a zero task has no piece);
* for every job, every piece of task `j'` starts no earlier than the end of every piece of
  every earlier task `j < j'` of the same job (task `j' ≥ 2` begins only after task `j' − 1`
  has completed; a zero task, having no piece, passes on the completion of the preceding
  tasks and occupies no processor time). -/
structure PreemptiveSchedule (F : FlowShop m J) where
  /-- the pieces `(s, f)` of task `j` of job `i` -/
  pieces : Fin m → J → Finset (ℝ × ℝ)
  start_nonneg : ∀ j i, ∀ p ∈ pieces j i, 0 ≤ p.1
  start_lt_end : ∀ j i, ∀ p ∈ pieces j i, p.1 < p.2
  disjoint : ∀ (j : Fin m) (i i' : J) (p p' : ℝ × ℝ), p ∈ pieces j i → p' ∈ pieces j i' →
    (i, p) ≠ (i', p') → p.2 ≤ p'.1 ∨ p'.2 ≤ p.1
  total_length : ∀ j i, ∑ p ∈ pieces j i, (p.2 - p.1) = F.t j i
  precedence : ∀ (i : J) (j j' : Fin m), j < j' →
    ∀ p ∈ pieces j i, ∀ p' ∈ pieces j' i, p.2 ≤ p'.1

namespace PreemptiveSchedule

variable {F : FlowShop m J}

/-- There are **no preemptions on processor `P_j`**: every task on `P_j` is processed in at
most one piece, i.e. in one contiguous interval (none if its time is zero). -/
def NoPreemptionOn (S : PreemptiveSchedule F) (j : Fin m) : Prop :=
  ∀ i, (S.pieces j i).card ≤ 1

/-- A **non-preemptive schedule** is a preemptive schedule with no preemptions on any
processor: every task is processed in at most one piece. -/
def IsNonPreemptive (S : PreemptiveSchedule F) : Prop :=
  ∀ j, S.NoPreemptionOn j

/-- The completion time of task `j` of job `i`: the latest end of a piece of task `j` or of an
earlier task of job `i`, and `0` if all of these have time zero. (For a task with positive
time this is the end of its last piece; a zero task completes when the previous task does.) -/
noncomputable def taskCompletion (S : PreemptiveSchedule F) (j : Fin m) (i : J) : ℝ :=
  (((Finset.univ : Finset (Fin m)).filter (fun j' => j' ≤ j)).biUnion
    (fun j' => S.pieces j' i)).fold max 0 Prod.snd

/-- `f_i(S)`, the time at which all tasks of job `i` have been completed: the latest end of a
piece of any task of job `i`, and `0` if every task of job `i` has time zero (the schedule
starts at time zero). -/
noncomputable def jobFinish (S : PreemptiveSchedule F) (i : J) : ℝ :=
  ((Finset.univ : Finset (Fin m)).biUnion (fun j => S.pieces j i)).fold max 0 Prod.snd

/-- The finish time `FT(S) = max_i f_i(S)` (with baseline `0`, the start of the schedule). -/
noncomputable def finishTime [Fintype J] (S : PreemptiveSchedule F) : ℝ :=
  (Finset.univ : Finset J).fold max 0 S.jobFinish

end PreemptiveSchedule

end FlowShop

end FlowJobShop.ThreePartFlow
