import Mathlib

namespace MatousekLP.Scheduling

/-- The total running time of the jobs that the schedule `σ` assigns to machine `i`
(Matoušek–Gärtner §8.3, p. 149): `∑_{j : σ(j) = i} d_ij`. Machines are `Fin m`, jobs are
`Fin n`, and `d i j` is the running time of job `j` on machine `i`. -/
def load {m n : ℕ} (d : Matrix (Fin m) (Fin n) ℝ) (σ : Fin n → Fin m) (i : Fin m) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j => σ j = i), d i j

/-- The makespan of the schedule `σ` (p. 149): the maximum over the machines of their load.
The index type `Fin m` is finite, so the supremum is a maximum whenever `m ≥ 1`. -/
noncomputable def makespan {m n : ℕ} (d : Matrix (Fin m) (Fin n) ℝ) (σ : Fin n → Fin m) : ℝ :=
  ⨆ i : Fin m, load d σ i

/-- `σ` is an optimal schedule (p. 149): its makespan is at most the makespan of every
schedule `τ : Fin n → Fin m`. The book's `t_opt` is `makespan d σ` for such a `σ`. -/
def IsOptimalSchedule {m n : ℕ} (d : Matrix (Fin m) (Fin n) ℝ) (σ : Fin n → Fin m) : Prop :=
  ∀ τ : Fin n → Fin m, makespan d σ ≤ makespan d τ

end MatousekLP.Scheduling
