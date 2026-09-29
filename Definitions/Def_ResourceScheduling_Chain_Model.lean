import Mathlib

/-!
# Unit-time scheduling on parallel identical machines with resource constraints

Błażewicz, Lenstra & Rinnooy Kan, *Scheduling subject to resource constraints: classification and
complexity*, Discrete Appl. Math. 5 (1983), pp. 12–13 (Section 2) and pp. 22–23 (Appendix),
specialised to parallel identical machines (`α₁ = P`), unit processing times (`p_j = 1`) and no
preemption (`β₁ = ∘`).

Conventions: jobs are `Fin n` and machines `Fin m` (0-based: job `J_{j+1}` is `j`); start times
are real numbers; job `j` is executed during the half-open interval `[S_j, S_j + 1)`.
-/

namespace ResourceScheduling.Chain

/-- An instance of a single-operation problem on `m` parallel identical machines with `n` unit-time
jobs, `l` resources of sizes `s h`, requirements `r h j` of job `j` for resource `h`, and the
precedence digraph `H` given by its list of arcs. -/
structure Instance where
  /-- number of jobs -/
  n : ℕ
  /-- number of machines -/
  m : ℕ
  /-- number of resources -/
  l : ℕ
  /-- resource sizes `s_h` -/
  s : Fin l → ℕ
  /-- resource requirements `r_hj` -/
  r : Fin l → Fin n → ℕ
  /-- the arcs of the precedence digraph `H` -/
  arcs : List (Fin n × Fin n)

namespace Instance

variable (I : Instance)

/-- `(j, k)` is an arc of `H`. -/
def Arc (j k : Fin I.n) : Prop := (j, k) ∈ I.arcs

/-- `J_j → J_k`: `H` contains a directed path (of positive length) from `j` to `k`. -/
def Prec (j k : Fin I.n) : Prop := Relation.TransGen I.Arc j k

/-- `H` is acyclic. -/
def Acyclic : Prop := ∀ j, ¬ I.Prec j j

/-- `β₃ = chain`: every vertex of `H` has indegree and outdegree at most one. -/
def IsChain : Prop :=
  ∀ v : Fin I.n,
    (Finset.univ.filter fun u => (u, v) ∈ I.arcs).card ≤ 1 ∧
    (Finset.univ.filter fun w => (v, w) ∈ I.arcs).card ≤ 1

/-- Every resource size is a positive integer. -/
def SizesPositive : Prop := ∀ h, 0 < I.s h

end Instance

/-- A nonpreemptive schedule: a machine and a real start time for every job. -/
structure Schedule (I : Instance) where
  /-- the machine processing each job -/
  machine : Fin I.n → Fin I.m
  /-- the start time `S_j` of each job -/
  start : Fin I.n → ℝ

namespace Schedule

variable {I : Instance} (σ : Schedule I)

/-- The completion time `C_j = S_j + 1` (unit processing time). -/
def completion (j : Fin I.n) : ℝ := σ.start j + 1

/-- Job `j` is being executed at time `t`, i.e. `t ∈ [S_j, S_j + 1)`. -/
def IsExecutedAt (j : Fin I.n) (t : ℝ) : Prop := σ.start j ≤ t ∧ t < σ.start j + 1

open Classical in
/-- Feasibility: nonnegative start times; two distinct jobs on the same machine do not overlap;
`J_j → J_k` implies `C_j ≤ S_k`; and at every real time `t`, for every resource `h`, the jobs being
executed at `t` require at most `s_h` in total. -/
def Feasible : Prop :=
  (∀ j, 0 ≤ σ.start j) ∧
  (∀ j k, j ≠ k → σ.machine j = σ.machine k →
      σ.completion j ≤ σ.start k ∨ σ.completion k ≤ σ.start j) ∧
  (∀ j k, I.Prec j k → σ.completion j ≤ σ.start k) ∧
  (∀ (t : ℝ) (h : Fin I.l),
      ∑ j ∈ Finset.univ.filter (fun j => σ.IsExecutedAt j t), I.r h j ≤ I.s h)

/-- The makespan `C_max = max_j C_j`, with `C_max = 0` when there are no jobs. -/
noncomputable def cmax : ℝ :=
  if h : 0 < I.n then Finset.univ.sup' ⟨⟨0, h⟩, Finset.mem_univ _⟩ σ.completion else 0

end Schedule

/-- The decision version: some feasible schedule has `C_max ≤ y`. -/
def Instance.HasScheduleWithin (I : Instance) (y : ℕ) : Prop :=
  ∃ σ : Schedule I, σ.Feasible ∧ σ.cmax ≤ (y : ℝ)

end ResourceScheduling.Chain
