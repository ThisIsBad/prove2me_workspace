import Mathlib

namespace GTWSched.MaxDisc

/-- The special form of the release times and deadlines (p. 342): for every task `i`,
either `d i - r i = l i + α`, or `r i = 0` and `d i < l i + α` (strict). -/
def SpecialForm {N : ℕ} (r d l : Fin N → ℝ) (α : ℝ) : Prop :=
  ∀ i, d i - r i = l i + α ∨ (r i = 0 ∧ d i < l i + α)

/-- A one-processor schedule is an execution order `σ` (`σ p` is the task executed in
position `p`) together with starting times `s`. `Ordered l σ s` says that a task finishes
no later than any task executed after it starts, so execution intervals meet at most at
their endpoints. -/
def Ordered {N : ℕ} (l : Fin N → ℝ) (σ : Fin N ≃ Fin N) (s : Fin N → ℝ) : Prop :=
  ∀ p q : Fin N, p < q → s (σ p) + l (σ p) ≤ s (σ q)

/-- Feasible (p. 342): every task begins no sooner than its release time and finishes no
later than its deadline. -/
def Feasible {N : ℕ} (r d l : Fin N → ℝ) (σ : Fin N ≃ Fin N) (s : Fin N → ℝ) : Prop :=
  Ordered l σ s ∧ ∀ i, r i ≤ s i ∧ s i + l i ≤ d i

/-- The makespan: the completion time of the latest finishing task. For `N = 0` the
supremum over the empty type is `0`. -/
noncomputable def makespan {N : ℕ} (l s : Fin N → ℝ) : ℝ :=
  ⨆ i : Fin N, s i + l i

/-- Optimum (p. 342): feasible and of minimum makespan among all feasible schedules. -/
def Optimum {N : ℕ} (r d l : Fin N → ℝ) (σ : Fin N ≃ Fin N) (s : Fin N → ℝ) : Prop :=
  Feasible r d l σ s ∧
    ∀ (σ' : Fin N ≃ Fin N) (s' : Fin N → ℝ), Feasible r d l σ' s' → makespan l s ≤ makespan l s'

/-- The release time property (p. 343) with respect to task `n`: every task executed after
`n` has a release time strictly later than the time at which `n` starts. -/
def ReleaseTimeProperty {N : ℕ} (r : Fin N → ℝ) (σ : Fin N ≃ Fin N) (s : Fin N → ℝ)
    (n : Fin N) : Prop :=
  ∀ i, σ.symm n < σ.symm i → s n < r i

/-- The completion time of the first part of a schedule, made of the tasks of index `< j`
(the paper's `T₁, …, Tⱼ`); it is `0` when `j = 0`, the finishing time of the paper's dummy
task `T₀`. -/
noncomputable def firstPartCompletion {N : ℕ} (l s : Fin N → ℝ) (j : ℕ) : ℝ :=
  ⨆ i : {i : Fin N // i.val < j}, s i.1 + l i.1

/-- Standard form with split index `j` (p. 344), for tasks indexed in nondecreasing deadline
order with the paper's `T_N` the last index `N - 1`:
the positions `< j` hold exactly the tasks of index `< j`, and these form an optimum
schedule of the sub-instance of those tasks; position `j` holds the last task, which starts at
the maximum of its release time and the completion time of the first part; positions
`j + 1, …, N - 1` hold the tasks of index `j, …, N - 2` in this order, each starting when the
preceding one finishes. -/
structure StandardForm {N : ℕ} (r d l : Fin N → ℝ) (σ : Fin N ≃ Fin N) (s : Fin N → ℝ)
    (j : ℕ) : Prop where
  split_lt : j < N
  first_part : ∀ p : Fin N, p.val < j → (σ p).val < j
  first_part_optimum :
    (∀ p q : Fin N, p < q → q.val < j → s (σ p) + l (σ p) ≤ s (σ q)) ∧
    (∀ i : Fin N, i.val < j → r i ≤ s i ∧ s i + l i ≤ d i) ∧
    ∀ (σ' : Fin j ≃ Fin j) (s' : Fin j → ℝ),
      Feasible (fun i => r (Fin.castLE split_lt.le i)) (fun i => d (Fin.castLE split_lt.le i))
        (fun i => l (Fin.castLE split_lt.le i)) σ' s' →
      firstPartCompletion l s j ≤ makespan (fun i => l (Fin.castLE split_lt.le i)) s'
  split_task : ∀ p : Fin N, p.val = j → (σ p).val + 1 = N
  split_start : ∀ p : Fin N, p.val = j → s (σ p) = max (r (σ p)) (firstPartCompletion l s j)
  after_order : ∀ p : Fin N, j < p.val → (σ p).val + 1 = p.val
  after_no_idle : ∀ p q : Fin N, j ≤ p.val → q.val = p.val + 1 → s (σ q) = s (σ p) + l (σ p)

end GTWSched.MaxDisc
