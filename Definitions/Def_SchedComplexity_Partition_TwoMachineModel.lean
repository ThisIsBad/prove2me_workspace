import Mathlib

namespace SchedComplexity.Partition

/-- A nonpreemptive schedule of `n` single-operation jobs `J_j`, `j < n`, on two identical
machines (Brucker, Lenstra & Rinnooy Kan 1975, Section 3, pp. 6–7, `ℓ = I`, `m = 2`): job `j` is
processed on machine `machine j` (machine `0` is the paper's `M_1`, machine `1` is `M_2`) from
its starting time `start j = B_j`, a natural number. -/
structure Schedule (n : ℕ) where
  machine : Fin n → Fin 2
  start : Fin n → ℕ

namespace Schedule

variable {n : ℕ}

/-- The completion time `C_j = B_j + p_j` of job `j` under processing times `p`. -/
def completion (p : Fin n → ℕ) (σ : Schedule n) (j : Fin n) : ℕ :=
  σ.start j + p j

/-- Feasibility: job `j` occupies its machine during the half-open interval `[B_j, B_j + p_j)`,
and two distinct jobs assigned to the same machine occupy disjoint intervals ("each machine can
handle at most one job at a time", p. 6). Two such intervals meet iff both are nonempty
(`0 < p_j`, `0 < p_k`) and each starts before the other ends; a job of processing time `0`
occupies the empty interval and conflicts with nothing. Idle time is allowed. -/
def IsFeasible (p : Fin n → ℕ) (σ : Schedule n) : Prop :=
  ∀ j k : Fin n, j ≠ k → σ.machine j = σ.machine k →
    ¬ (0 < p j ∧ 0 < p k ∧ σ.start j < σ.start k + p k ∧ σ.start k < σ.start j + p j)

/-- A feasible schedule in which each machine processes its jobs without idle time from time
`0`: every job assigned to a machine completes by the total processing time of the jobs on that
machine (together with feasibility, the jobs of each machine then fill `[0, Σ p)` exactly). -/
def IsNonIdle (p : Fin n → ℕ) (σ : Schedule n) : Prop :=
  σ.IsFeasible p ∧
    ∀ j : Fin n, σ.completion p j ≤
      ∑ k ∈ Finset.univ.filter (fun k => σ.machine k = σ.machine j), p k

/-- The total weighted completion time `Σ_j w_j C_j` (p. 7). -/
def sumWC (p w : Fin n → ℕ) (σ : Schedule n) : ℕ :=
  ∑ j : Fin n, w j * σ.completion p j

end Schedule

end SchedComplexity.Partition
