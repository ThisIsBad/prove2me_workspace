import Mathlib

namespace FlowJobShop.PairGroups

/-- A **flow shop** (Gonzalez–Sahni 1978, p. 36) with `m` processors `P_1, …, P_m`, indexed by
`Fin m` (`P_1 = 0`), and `n` jobs, indexed by `Fin n`. Task `j` of job `i` is performed on
processor `P_j` and takes time `t j i = t_{j,i} ≥ 0`; zero task times are allowed. -/
structure FlowShop (m n : ℕ) where
  /-- the processing time `t_{j,i}` of task `j` of job `i` -/
  t : Fin m → Fin n → ℝ
  t_nonneg : ∀ j i, 0 ≤ t j i

namespace FlowShop

variable {m n : ℕ}

/-- A **non-preemptive schedule** of the flow shop `F` is given by start times: task `j` of job
`i` is processed on `P_j` without interruption during `[s j i, s j i + t_{j,i})`. It is
**feasible** when
1. it starts at time zero: every `s j i ≥ 0`;
2. for every job, task `j + 1` starts only after task `j` has completed:
   `s j i + t_{j,i} ≤ s (j+1) i`;
3. two tasks of different jobs with positive times on the same processor do not overlap
   (their half-open intervals are disjoint). A task of time zero occupies no processor time. -/
def IsFeasible (F : FlowShop m n) (s : Fin m → Fin n → ℝ) : Prop :=
  (∀ j i, 0 ≤ s j i) ∧
  (∀ (i : Fin n) (j j' : Fin m), j.val + 1 = j'.val → s j i + F.t j i ≤ s j' i) ∧
  (∀ (j : Fin m) (i i' : Fin n), i ≠ i' → 0 < F.t j i → 0 < F.t j i' →
      s j i + F.t j i ≤ s j i' ∨ s j i' + F.t j i' ≤ s j i)

/-- The **finish time** `FT(s)`: the time at which all tasks of all jobs have been completed,
i.e. the largest completion time `s j i + t_{j,i}`, with baseline `0` (the schedule starts at
time zero; `FT = 0` when there is no task). -/
noncomputable def finishTime (F : FlowShop m n) (s : Fin m → Fin n → ℝ) : ℝ :=
  (Finset.univ : Finset (Fin m × Fin n)).fold max 0 (fun p => s p.1 p.2 + F.t p.1 p.2)

/-- An **optimal finish time (OFT) schedule**: a feasible schedule whose finish time is at most
that of every feasible schedule of the same flow shop. -/
def IsOptimal (F : FlowShop m n) (s : Fin m → Fin n → ℝ) : Prop :=
  F.IsFeasible s ∧ ∀ s' : Fin m → Fin n → ℝ, F.IsFeasible s' → F.finishTime s ≤ F.finishTime s'

end FlowShop

end FlowJobShop.PairGroups
