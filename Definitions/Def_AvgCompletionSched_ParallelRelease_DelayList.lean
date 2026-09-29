import Mathlib
import Definitions.Def_AvgCompletionSched_ParallelRelease_Model

namespace AvgCompletionSched.ParallelRelease

open MeasureTheory

variable {n m : ℕ}

/-- The data of a run of the continuous-time algorithm Delay List (§4.1, pp. 158–159) on an
instance without precedence constraints: start times `S`, machines `M`, the left end `τ j` of the
time window from which job `j` takes its charged idle time, and the order `ev` in which the
algorithm schedules the jobs (`ev a` is the `a`-th job scheduled; several jobs may be scheduled at
the same instant, one after the other). -/
structure DelayListRun (I : Instance n m) where
  /-- start times -/
  S : Fin n → ℝ
  /-- machine assignment -/
  M : Fin n → Fin m
  /-- left end of the charge window of each job -/
  τ : Fin n → ℝ
  /-- scheduling order: `ev a` is the `a`-th job the algorithm schedules -/
  ev : Fin n ≃ Fin n

namespace DelayListRun

variable {I : Instance n m} (D : DelayListRun I)

/-- Completion time `C^D_j = S_j + p_j`. -/
def C (j : Fin n) : ℝ := D.S j + I.p j

/-- Job `k` is scheduled by the algorithm before job `j`. -/
def Before (k j : Fin n) : Prop := D.ev.symm k < D.ev.symm j

/-- Number of idle machines at time `t`: `m` minus the number of jobs running at `t`. -/
noncomputable def idle (t : ℝ) : ℝ :=
  (m : ℝ) - ((Finset.univ.filter fun k => D.S k ≤ t ∧ t < D.S k + I.p k).card : ℝ)

/-- The charge window of job `j`: the open interval `(τ j, S j)`. -/
def window (j : Fin n) : Set ℝ := Set.Ioo (D.τ j) (D.S j)

/-- Idle time (machine × time) charged to job `j`: the idle time in its window that no job
scheduled before `j` has already charged. -/
noncomputable def charge (j : Fin n) : ℝ :=
  ∫ t in D.window j \ ⋃ k ∈ {k | D.Before k j}, D.window k, D.idle t

/-- Uncharged idle time accumulated during `[0, S j)` at the moment `j` is scheduled, i.e. after
the charges of the jobs scheduled before `j`. -/
noncomputable def unchargedAt (j : Fin n) : ℝ :=
  ∫ t in Set.Ico 0 (D.S j) \ ⋃ k ∈ {k | D.Before k j}, D.window k, D.idle t

/-- Uncharged idle time accumulated during `[0, t)` once every job starting at or before `t` has
been scheduled and charged. -/
noncomputable def unchargedAfter (t : ℝ) : ℝ :=
  ∫ s in Set.Ico 0 t \ ⋃ k ∈ {k | D.S k ≤ t}, D.window k, D.idle s

end DelayListRun

/-- `D` is a run of the continuous-time Delay List algorithm with parameter `β` on the list `π`
(`π k` is the `k`-th job of the list), for jobs without precedence constraints, so that a job is
ready exactly from its release date on (§4.1, pp. 158–159, with the continuous-time rule of the
proof of Fact 4.6, p. 159). Writing `pos j` for the list position of `j`:

1. (feasibility) every job starts no earlier than its release date, on a machine on which every
   job scheduled earlier has finished; jobs are scheduled in nondecreasing order of start time;
2. (the two scheduling cases) each job `j`, when it is scheduled, is either
   * *case 1*: the first job of the list among the jobs not yet scheduled; it is charged all
     uncharged idle time in `(r j, S j)` (`τ j = r j`); or
   * *case 2*: the first job of the list among the unscheduled jobs is not ready at `S j`, `j` is
     the first ready unscheduled job of the list, at least `β p j` uncharged idle time has
     accumulated, and `j` is charged exactly `β p j` of it, taken from the most recent uncharged
     idle time (the window `(τ j, S j)` with `0 ≤ τ j ≤ S j`);
3. (no delay) at every time `t ≥ 0` at which some machine is idle, once all jobs starting at or
   before `t` are scheduled, neither case applies: the first unscheduled job of the list is not
   ready, and the first ready unscheduled job `k` (if any) has less than `β p k` uncharged idle
   time available. -/
def IsDelayListSchedule (I : Instance n m) (π : Fin n ≃ Fin n) (β : ℝ) (D : DelayListRun I) :
    Prop :=
  -- feasibility
  (∀ j, I.r j ≤ D.S j) ∧
  (∀ j k, D.Before k j → D.S k ≤ D.S j) ∧
  (∀ j k, D.Before k j → D.M k = D.M j → D.S k + I.p k ≤ D.S j) ∧
  -- the two scheduling cases
  (∀ j,
    ((∀ k, ¬ D.Before k j → π.symm j ≤ π.symm k) ∧ D.τ j = I.r j) ∨
    ((∀ h, ¬ D.Before h j → (∀ k, ¬ D.Before k j → π.symm h ≤ π.symm k) → D.S j < I.r h) ∧
      (∀ k, ¬ D.Before k j → I.r k ≤ D.S j → π.symm j ≤ π.symm k) ∧
      β * I.p j ≤ D.unchargedAt j ∧
      0 ≤ D.τ j ∧ D.τ j ≤ D.S j ∧
      D.charge j = β * I.p j)) ∧
  -- no delay
  (∀ t, 0 ≤ t → (∃ μ : Fin m, ∀ k, D.M k = μ → ¬ (D.S k ≤ t ∧ t < D.S k + I.p k)) →
    (∀ h, t < D.S h → (∀ k, t < D.S k → π.symm h ≤ π.symm k) → t < I.r h) ∧
    (∀ k, t < D.S k → I.r k ≤ t → (∀ l, t < D.S l → I.r l ≤ t → π.symm k ≤ π.symm l) →
      D.unchargedAfter t < β * I.p k))

end AvgCompletionSched.ParallelRelease
