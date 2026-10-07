import Mathlib

namespace SchrageSRPT.Opt

open MeasureTheory

/-- A **schedule** of the arrival stream with arrival times `A` (Schrage 1968, DEFINITIONS,
p. 688): `δ n t ∈ {0, 1}` says whether the processor is devoted to job `n` at time `t`;
each `δ n` is measurable; no job is processed before it arrives (`δ n t = 0` for `t < A n`);
and the processor is devoted to at most one job at a time (the page's `Σ_n δ(n, t) ≤ 1`). -/
def IsSchedule (A : ℕ → ℝ) (δ : ℕ → ℝ → ℝ) : Prop :=
  (∀ n t, δ n t = 0 ∨ δ n t = 1) ∧
  (∀ n, Measurable (δ n)) ∧
  (∀ n t, t < A n → δ n t = 0) ∧
  (∀ t n m, δ n t = 1 → δ m t = 1 → n = m)

/-- The processing time remaining for job `n` at time `t`,
`S(n, t) = P(n) - ∫_{A(n)}^{t} δ(n, x) dx` (p. 688). -/
noncomputable def remaining (A P : ℕ → ℝ) (δ : ℕ → ℝ → ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  P n - ∫ x in (A n)..t, δ n x

/-- The set of times `x ≥ A(n)` by which job `n` has received its processing time,
`{x : ∫_{A(n)}^{x} δ(n, t) dt ≥ P(n)}` (p. 688). -/
def completedBy (A P : ℕ → ℝ) (δ : ℕ → ℝ → ℝ) (n : ℕ) : Set ℝ :=
  {x | A n ≤ x ∧ P n ≤ ∫ t in (A n)..x, δ n t}

open Classical in
/-- The completion time `C(n) = min {x : ∫_{A(n)}^{x} δ(n, t) dt ≥ P(n)}` (p. 688), with value
`⊤` when job `n` never receives its processing time. -/
noncomputable def completion (A P : ℕ → ℝ) (δ : ℕ → ℝ → ℝ) (n : ℕ) : WithTop ℝ :=
  if (completedBy A P δ n).Nonempty then ((sInf (completedBy A P δ n) : ℝ) : WithTop ℝ) else ⊤

/-- The set `θ(t)` of jobs in system at time `t` (p. 688): the jobs that have arrived and still
have positive remaining processing time. -/
def inSystem (A P : ℕ → ℝ) (δ : ℕ → ℝ → ℝ) (t : ℝ) : Set ℕ :=
  {n | A n ≤ t ∧ 0 < remaining A P δ n t}

/-- The number `N(t)` of jobs in system at time `t` (p. 688). It is a genuine count when only
finitely many jobs have arrived by time `t`. -/
noncomputable def numInSystem (A P : ℕ → ℝ) (δ : ℕ → ℝ → ℝ) (t : ℝ) : ℕ :=
  (inSystem A P δ t).ncard

/-- The **SRPT discipline** (p. 687): "the processor should at all times process that job of
those available, which has the shortest remaining processing time". At every time `t` at which
some job is in system, the processor serves a job in system whose remaining processing time is
smallest among the jobs in system (ties broken arbitrarily). -/
def IsSRPT (A P : ℕ → ℝ) (δ : ℕ → ℝ → ℝ) : Prop :=
  IsSchedule A δ ∧
  ∀ t, (inSystem A P δ t).Nonempty →
    ∃ k ∈ inSystem A P δ t, δ k t = 1 ∧
      ∀ j ∈ inSystem A P δ t, remaining A P δ k t ≤ remaining A P δ j t

/-- The revised schedule of case (b1) of PROOF (p. 689): job `j` is processed throughout
`[t, t + v]` ("setting `δ_r(j, x) = 1` for `t ≤ x ≤ t + v`"), every other job is switched off
there, and the original schedule `δo` is kept outside `[t, t + v]`. -/
noncomputable def idleFill (δo : ℕ → ℝ → ℝ) (j : ℕ) (t v : ℝ) : ℕ → ℝ → ℝ :=
  fun n x => if t ≤ x ∧ x ≤ t + v then (if n = j then 1 else 0) else δo n x

/-- The revised schedule of case (b2) of PROOF (p. 689): from time `t` on, the processing
capacity `δo(j, x) + δo(k, x)` that the original schedule `δo` devotes to the pair `{j, k}` is
reassigned to them according to SRPT with `j` first: `j` receives all of it until it has received
its remaining time `S_o(j, t)`, and `k` receives it afterwards. Before `t`, and for every other
job, `δo` is unchanged. -/
noncomputable def srptReassign (A P : ℕ → ℝ) (δo : ℕ → ℝ → ℝ) (j k : ℕ) (t : ℝ) :
    ℕ → ℝ → ℝ :=
  fun n x =>
    if x < t then δo n x
    else if n = j then
      (if (∫ y in t..x, (δo j y + δo k y)) < remaining A P δo j t then δo j x + δo k x else 0)
    else if n = k then
      (δo j x + δo k x) -
        (if (∫ y in t..x, (δo j y + δo k y)) < remaining A P δo j t then δo j x + δo k x else 0)
    else δo n x

end SchrageSRPT.Opt
