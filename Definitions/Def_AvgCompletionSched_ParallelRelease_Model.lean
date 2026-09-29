import Mathlib

namespace AvgCompletionSched.ParallelRelease

open MeasureTheory

/-- An instance of nonpreemptive scheduling on `m` identical parallel machines with release dates
(Chekuri–Motwani–Natarajan–Stein 2001, §1, pp. 146–147, and §3, p. 156): `n` jobs `0, …, n-1`,
job `j` has processing time `p j > 0` and release date `r j ≥ 0`; there is at least one machine.
The objective is the (unweighted) total completion time. -/
structure Instance (n m : ℕ) where
  /-- processing times -/
  p : Fin n → ℝ
  /-- release dates -/
  r : Fin n → ℝ
  p_pos : ∀ j, 0 < p j
  r_nonneg : ∀ j, 0 ≤ r j
  m_pos : 0 < m

variable {n m : ℕ}

/-- A feasible nonpreemptive schedule on the `m` machines: job `j` runs without interruption on
machine `M j` during `[S j, S j + p j)`, not before its release date, and two different jobs on
the same machine do not overlap. -/
structure Schedule (I : Instance n m) where
  /-- start times -/
  S : Fin n → ℝ
  /-- machine assignment -/
  M : Fin n → Fin m
  released : ∀ j, I.r j ≤ S j
  noOverlap : ∀ i j, M i = M j → i ≠ j → S i + I.p i ≤ S j ∨ S j + I.p j ≤ S i

/-- Completion time `C_j = S_j + p_j` of job `j` in a nonpreemptive schedule. -/
def Schedule.C {I : Instance n m} (N : Schedule I) (j : Fin n) : ℝ :=
  N.S j + I.p j

/-- A preemptive schedule for the one-machine relaxation `I1` (p. 156): one machine of unit speed,
job `j` has processing time `p j / m` and release date `r j`. It is given by processing rates:
`ρ j t ≥ 0` is the rate at which job `j` is processed at time `t`; the rates at any time sum to at
most `1`; a job is not processed before its release date; it receives exactly `p j / m` units of
processing in total; and it is processed only before some finite time. Rates allow the machine to
be shared among several jobs at once. -/
structure RelaxSchedule (I : Instance n m) where
  /-- processing rate of each job at each time -/
  ρ : Fin n → ℝ → ℝ
  measurable : ∀ j, Measurable (ρ j)
  integrable : ∀ j, Integrable (ρ j)
  nonneg : ∀ j t, 0 ≤ ρ j t
  capacity : ∀ t, ∑ j, ρ j t ≤ 1
  released : ∀ j t, t < I.r j → ρ j t = 0
  total : ∀ j, ∫ t, ρ j t = I.p j / m
  bounded : ∀ j, ∃ T : ℝ, ∀ t, T ≤ t → ρ j t = 0

/-- Amount of job `j` processed in the relaxation schedule `P` before time `t`. -/
noncomputable def RelaxSchedule.done {I : Instance n m} (P : RelaxSchedule I) (j : Fin n)
    (t : ℝ) : ℝ :=
  ∫ s in Set.Iio t, P.ρ j s

/-- Completion time `C^{P1}_j` of job `j` in the relaxation schedule `P`: the first time by which
all `p j / m` units of `j` have been processed. -/
noncomputable def RelaxSchedule.CP {I : Instance n m} (P : RelaxSchedule I) (j : Fin n) : ℝ :=
  sInf {t | I.p j / m ≤ P.done j t}

/-- `P` is an optimal preemptive schedule for the one-machine relaxation `I1`: its total
completion time is at most that of every preemptive schedule of `I1`. -/
def RelaxSchedule.IsOptimal {I : Instance n m} (P : RelaxSchedule I) : Prop :=
  ∀ Q : RelaxSchedule I, ∑ j, P.CP j ≤ ∑ j, Q.CP j

/-- The list `π` (`π k` is the `k`-th job of the list) orders the jobs by their completion times
in `P`, ties in any order (p. 157). -/
def IsCompletionOrder {I : Instance n m} (P : RelaxSchedule I) (π : Fin n ≃ Fin n) : Prop :=
  ∀ k l : Fin n, k ≤ l → P.CP (π k) ≤ P.CP (π l)

/-- Strict-order list scheduling on `m` machines (the list schedule `N` of §3, p. 157). The jobs
are taken in the order of the list `π`; the state after the first `k` jobs of the list is the
vector of machine free times together with the start time of the `k`-th job. Job `π k` starts at
the earliest time that is no earlier than its release date, no earlier than the start of the
previous job of the list, and at which some machine is free; it is put on a machine that became
free earliest. -/
noncomputable def listRun (I : Instance n m) (π : Fin n ≃ Fin n) : ℕ → (Fin m → ℝ) × ℝ
  | 0 => (fun _ => 0, 0)
  | k + 1 =>
    if h : k < n then
      let f := (listRun I π k).1
      let L := (listRun I π k).2
      let j := π ⟨k, h⟩
      let μ : Fin m := Classical.choose
        (Finset.exists_min_image Finset.univ f ⟨⟨0, I.m_pos⟩, Finset.mem_univ _⟩)
      let s := max (max (I.r j) L) (f μ)
      (Function.update f μ (s + I.p j), s)
    else listRun I π k

/-- Start time of job `j` in the strict-order list schedule with list `π`. -/
noncomputable def listStart (I : Instance n m) (π : Fin n ≃ Fin n) (j : Fin n) : ℝ :=
  (listRun I π ((π.symm j : ℕ) + 1)).2

/-- Completion time `C^N_j` of job `j` in the strict-order list schedule with list `π`. -/
noncomputable def listCompletion (I : Instance n m) (π : Fin n ≃ Fin n) (j : Fin n) : ℝ :=
  listStart I π j + I.p j

end AvgCompletionSched.ParallelRelease
