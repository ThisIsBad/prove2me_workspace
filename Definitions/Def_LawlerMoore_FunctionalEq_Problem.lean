import Mathlib

namespace LawlerMoore.FunctionalEq

/-! The two-mode, fixed-order problem of Lawler and Moore (1969), Section 1, p. 77.

There are `n` jobs, `Fin n`, performed one at a time in the fixed order `0, 1, …, n - 1`
(Lean job `i` is the paper's job `i + 1`). A mode assignment is `m : Fin n → Bool`:
`m i = true` is the first mode (processing time `a i`, loss `α i (completion time)`),
`m i = false` the other mode (processing time `b i`, loss `β i (completion time)`).
Time is a nonnegative integer. A timing is a vector of completion times `c : Fin n → ℕ`;
idle time between jobs is allowed. -/

/-- The processing time of job `i` under the mode assignment `m`: `a i` in the first mode,
`b i` in the other. -/
def procTime {n : ℕ} (a b : Fin n → ℕ) (m : Fin n → Bool) (i : Fin n) : ℕ :=
  if m i then a i else b i

/-- `doneAt c k` is the completion time of the paper's job `k`, i.e. of Lean job `k - 1`,
for `1 ≤ k ≤ n`, and `0` for `k = 0` (nothing is processed before time `0`). For `k > n`
the value is `0` and is never used. -/
def doneAt {n : ℕ} (c : Fin n → ℕ) (k : ℕ) : ℕ :=
  if h : 0 < k ∧ k ≤ n then c ⟨k - 1, by omega⟩ else 0

/-- `IsFeasible a b m c j`: the completion times `c` are a feasible timing of the first `j`
jobs under the mode assignment `m`. Each of these jobs starts no earlier than the completion
of the previous job (time `0` for the first job) and runs for its processing time, so
`c_{i-1} + p_i ≤ c_i`; idle time is allowed. The values of `m` and `c` on the jobs after the
first `j` are irrelevant. -/
def IsFeasible {n : ℕ} (a b : Fin n → ℕ) (m : Fin n → Bool) (c : Fin n → ℕ) (j : ℕ) : Prop :=
  ∀ i : Fin n, i.val < j → doneAt c i.val + procTime a b m i ≤ c i

/-- The total loss of the first `j` jobs under modes `m` and completion times `c`:
`∑_{i < j}` of `α i (c i)` if job `i` runs in the first mode, and `β i (c i)` otherwise. -/
def totalLoss {n : ℕ} (α β : Fin n → ℕ → ℝ) (m : Fin n → Bool) (c : Fin n → ℕ) (j : ℕ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < j), if m i then α i (c i) else β i (c i)

/-- The set of total losses of the first `j` jobs over all mode assignments and all feasible
timings in which the paper's job `j` is completed no later than time `t` (for `j = 0` the
constraint reads `0 ≤ t`). Its least element, when it exists, is the paper's
"minimum total loss for the first `j` jobs, subject to the constraint that job `j` is
completed no later than time `t`". -/
def lossesBy {n : ℕ} (a b : Fin n → ℕ) (α β : Fin n → ℕ → ℝ) (j : ℕ) (t : ℤ) : Set ℝ :=
  {L | ∃ (m : Fin n → Bool) (c : Fin n → ℕ),
    IsFeasible a b m c j ∧ ((doneAt c j : ℕ) : ℤ) ≤ t ∧ L = totalLoss α β m c j}

end LawlerMoore.FunctionalEq
