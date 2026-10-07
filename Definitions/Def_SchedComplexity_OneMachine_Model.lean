import Mathlib

namespace SchedComplexity.OneMachine

/-- A single-machine instance in the sense of Section 3 (Brucker, Lenstra & Rinnooy Kan, Report
BW 43/75, p. 6): `n` jobs `J_1, …, J_n`, here `Fin n` (0-based, so `J_j` is index `j - 1` and the
last job `J_n` is index `n - 1`), each with one operation on the machine `M_1`, a processing time
`p j`, a weight `w j`, a release date `r j` and a due date `d j`, all nonnegative integers. -/
structure Instance where
  /-- The number of jobs. -/
  n : ℕ
  /-- Processing times `p_{j1}`. -/
  p : Fin n → ℕ
  /-- Weights `w_j`. -/
  w : Fin n → ℕ
  /-- Release dates `r_j`. -/
  r : Fin n → ℕ
  /-- Due dates `d_j`. -/
  d : Fin n → ℕ

namespace Instance

variable (I : Instance)

/-- A feasible schedule on the single machine, given by starting times `B j ∈ ℕ`: each job
starts no earlier than its release date, and the occupied half-open intervals
`[B j, B j + p j)` of distinct jobs are disjoint (Section 3, p. 6). Idle time is allowed.
In particular, a zero-processing-time job occupies the empty interval, as the paper's
nonnegative processing-time convention requires. Start times are natural numbers: Section 3
computes `B_j` from processing orders on integer data. -/
def IsFeasible (B : Fin I.n → ℕ) : Prop :=
  (∀ j, I.r j ≤ B j) ∧
    ∀ j k, j ≠ k →
      Disjoint (Set.Ico (B j) (B j + I.p j)) (Set.Ico (B k) (B k + I.p k))

/-- The completion time `C_j = B_j + p_{j1}`. -/
def C (B : Fin I.n → ℕ) (j : Fin I.n) : ℕ := B j + I.p j

/-- The lateness `L_j = C_j - d_j`, an integer (it may be negative). -/
def lateness (B : Fin I.n → ℕ) (j : Fin I.n) : ℤ := (I.C B j : ℤ) - I.d j

/-- `U_j = if C_j ≤ d_j then 0 else 1`. -/
def U (B : Fin I.n → ℕ) (j : Fin I.n) : ℕ := if I.C B j ≤ I.d j then 0 else 1

/-- The criterion `∑ w_j C_j = ∑_{j=1}^n w_j C_j` (p. 7). -/
def sumWC (B : Fin I.n → ℕ) : ℕ := ∑ j, I.w j * I.C B j

/-- The criterion `∑ w_j U_j = ∑_{j=1}^n w_j U_j` (p. 7): the total weight of the late jobs. -/
def sumWU (B : Fin I.n → ℕ) : ℕ := ∑ j, I.w j * I.U B j

/-- Default class: all jobs are available at time `0` (`r_j = 0` for every job, p. 6). -/
def AllReleasedAtZero : Prop := ∀ j, I.r j = 0

/-- The class element `r_n ≥ 0` (p. 7): there is at least one job, and every job except the last
one, `J_n` (index `n - 1`), has release date `0`; `J_n` may have any release date. -/
def OnlyLastReleased : Prop := 0 < I.n ∧ ∀ j : Fin I.n, (j : ℕ) + 1 < I.n → I.r j = 0

/-- The class element `w_j = 1` (p. 7): all weights equal one. -/
def UnitWeights : Prop := ∀ j, I.w j = 1

/-- The binary-coded data of an instance with threshold `y`, as a list of naturals: the number of
jobs `n`, then for each job `J_1, …, J_n` in turn its data `p_{j1}, w_j, r_j, d_j`, then `y`.
This list determines the instance and `y`. -/
def codeList (y : ℕ) : List ℕ :=
  I.n :: ((List.ofFn fun j : Fin I.n => [I.p j, I.w j, I.r j, I.d j]).flatten ++ [y])

end Instance

end SchedComplexity.OneMachine
