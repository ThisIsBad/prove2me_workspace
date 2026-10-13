import Mathlib

namespace NumStochOpt.ListScheduling

/-- The load of machine `i` under the assignment `σ` of the first `n` jobs to `m` identical
machines: the sum of the processing times `p j` of the jobs `j < n` with `σ j = i`.
Job `j` (0-based) is the book's job `j + 1`. -/
def machineLoad {n m : ℕ} (p : ℕ → ℝ) (σ : Fin n → Fin m) (i : Fin m) : ℝ :=
  ∑ j : Fin n, if σ j = i then p (j : ℕ) else 0

/-- The makespan of the assignment `σ`: the maximum load of any one machine
(Rinnooy Kan–Stougie, Ch. 8 of Ermoliev & Wets (1988), p. 205). -/
noncomputable def makespan {n m : ℕ} (p : ℕ → ℝ) (σ : Fin n → Fin m) : ℝ :=
  ⨆ i : Fin m, machineLoad p σ i

/-- The minimum makespan `C*_n(m)` of the first `n` jobs (processing times `p 0, …, p (n-1)`)
on `m` identical machines: the minimum over all assignments `σ : Fin n → Fin m` of the
makespan. Only meaningful for `m ≥ 1`; every theorem assumes it. -/
noncomputable def optMakespan (n m : ℕ) (p : ℕ → ℝ) : ℝ :=
  ⨅ σ : Fin n → Fin m, makespan p σ

/-- `p_max = max_{j = 1, …, n} p_j`, the largest of the first `n` processing times
(`0` when `n = 0`). -/
noncomputable def maxProcTime (n : ℕ) (p : ℕ → ℝ) : ℝ :=
  ⨆ j : Fin n, p (j : ℕ)

end NumStochOpt.ListScheduling
