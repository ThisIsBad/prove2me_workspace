import Mathlib

namespace FlowJobShop.PartitionFlow

/-- A flow shop (Gonzalez–Sahni 1978, p. 36): `m` processors `P_1, …, P_m`, indexed by `Fin m`
(`P_1 = 0`), and a set of jobs indexed by a type `J`. Task `j` of job `i` must be performed on
processor `P_j` and takes time `t j i = t_{j,i} ≥ 0`. Zero task times are allowed. -/
structure FlowShop (m : ℕ) (J : Type*) where
  /-- processing time `t_{j,i}` of task `j` of job `i` -/
  t : Fin m → J → ℝ
  t_nonneg : ∀ j i, 0 ≤ t j i
  /-- the paper assumes at least one processor -/
  m_pos : 0 < m

namespace FlowShop

variable {m : ℕ} {J : Type*}

/-- A **preemptive schedule** of a flow shop, in the paper's own representation (footnote 1,
p. 40): the work of processor `P_j` is a finite collection of pieces, a piece `(s, f)` of task
`j` of job `i` meaning that this task is processed on `P_j` during `[s, f)`.
`pieces j i` is the finite set of pieces of task `j` of job `i`; every piece of that task is
therefore on the task's own processor `P_j`. The conditions are:
* every piece satisfies `0 ≤ s < f` (the schedule starts at time zero);
* two different pieces on the same processor are disjoint as half-open intervals;
* the pieces of a task have total length equal to the task time (so a zero task has no piece);
* for every job, every piece of task `j'` starts no earlier than the end of every piece of
  every earlier task `j < j'` of the same job (task `j' ≥ 2` begins only after task `j' − 1`
  has completed; a zero task, having no piece, imposes the completion of the preceding tasks). -/
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

/-- A **non-preemptive schedule** is a preemptive schedule in which every task is processed
in at most one piece (exactly one if its time is positive, none if it is zero). -/
def IsNonPreemptive (S : PreemptiveSchedule F) : Prop :=
  ∀ j i, (S.pieces j i).card ≤ 1

/-- `f_i(S)`, the time at which all tasks of job `i` have been completed: the latest end of a
piece of any task of job `i`, and `0` if every task of job `i` has time zero (the schedule
starts at time zero). -/
noncomputable def jobFinish (S : PreemptiveSchedule F) (i : J) : ℝ :=
  ((Finset.univ : Finset (Fin m)).biUnion (fun j => S.pieces j i)).fold max 0 Prod.snd

/-- The finish time `FT(S) = max_i f_i(S)` (with baseline `0`, the start of the schedule). -/
noncomputable def finishTime [Fintype J] (S : PreemptiveSchedule F) : ℝ :=
  (Finset.univ : Finset J).fold max 0 S.jobFinish

end PreemptiveSchedule

/-- The flow shop has **at most two nonzero tasks per job**: for every job `i`, at most two of
`t_{1,i}, …, t_{m,i}` are nonzero. -/
def AtMostTwoNonzeroTasks (F : FlowShop m J) : Prop :=
  ∀ i, ((Finset.univ : Finset (Fin m)).filter (fun j => F.t j i ≠ 0)).card ≤ 2

end FlowShop

end FlowJobShop.PartitionFlow
