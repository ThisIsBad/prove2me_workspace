import Mathlib

namespace SchedComplexity.Tardiness

/-! # The single-machine total weighted tardiness problem `n|1||Σw_jT_j`

Brucker, Lenstra & Rinnooy Kan 1975, Section 3 (pp. 6–7). Jobs form a finite type `J`; job `j`
has processing time `p j`, weight `w j` and due date `d j`, all in `ℕ` (zero allowed); all release
dates are `0`. A schedule assigns every job a start time in `ℕ`. -/

/-- A schedule `S` (start times) on one machine is feasible iff no two distinct jobs overlap:
job `j` occupies `[S j, S j + p j)`, so for `i ≠ j` one of them finishes before the other starts.
Start times are natural numbers, hence `≥ 0 = r_j`. -/
def IsFeasible {J : Type*} (p : J → ℕ) (S : J → ℕ) : Prop :=
  ∀ i j : J, i ≠ j → S i + p i ≤ S j ∨ S j + p j ≤ S i

/-- Completion time `C_j = B_j + p_j` of job `j` under the start times `S`. -/
def completion {J : Type*} (p : J → ℕ) (S : J → ℕ) (j : J) : ℕ :=
  S j + p j

/-- Tardiness `T_j = max{0, C_j − d_j}`, computed in `ℤ`. -/
def tardiness {J : Type*} (p d : J → ℕ) (S : J → ℕ) (j : J) : ℤ :=
  max 0 ((completion p S j : ℤ) - d j)

/-- Total weighted tardiness `Σ_j w_j T_j` of the schedule `S`. -/
def totalWeightedTardiness {J : Type*} [Fintype J] (p w d : J → ℕ) (S : J → ℕ) : ℤ :=
  ∑ j, (w j : ℤ) * tardiness p d S j

/-- The instance `(p, w, d)` of `n|1||Σw_jT_j` with threshold `y` is a yes-instance: some feasible
schedule has `Σ_j w_j T_j ≤ y`. -/
def HasScheduleLE {J : Type*} [Fintype J] (p w d : J → ℕ) (y : ℕ) : Prop :=
  ∃ S : J → ℕ, IsFeasible p S ∧ totalWeightedTardiness p w d S ≤ (y : ℤ)

/-! ## Processing orders and their schedules without idle time

Jobs `Fin n`; a processing order is a permutation `π` with `π i` the job in the (0-based) position
`i`, i.e. the paper's `π(i+1)`. -/

/-- `C_π(k)` for the paper's 1-based position `k`: the completion time of the `k`-th job when the
jobs are processed in the order `π` without interruption from time `0`, namely the total
processing time of the first `k` positions, `Σ_{i < k} p_{π(i)}` (0-based `i`). It is `0` for
`k = 0` and `Σ_j p_j` for `k ≥ n`. -/
def posCompletion {n : ℕ} (p : Fin n → ℕ) (π : Equiv.Perm (Fin n)) (k : ℕ) : ℕ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k), p (π i)

/-- The start times of the schedule without idle time of the order `π`: job `j`, in the 0-based
position `π⁻¹ j`, starts when the jobs in the earlier positions are finished. Its completion time
is `posCompletion p π ((π⁻¹ j) + 1)`. -/
def noIdleStart {n : ℕ} (p : Fin n → ℕ) (π : Equiv.Perm (Fin n)) : Fin n → ℕ :=
  fun j => posCompletion p π (π.symm j).val

/-- `Σ_j w_j T_j` of the schedule without idle time of the order `π`. -/
def orderTWT {n : ℕ} (p w d : Fin n → ℕ) (π : Equiv.Perm (Fin n)) : ℤ :=
  totalWeightedTardiness p w d (noIdleStart p π)

/-- `Σ_{j > t} v_{π(j)} (C_π(j) − C_π(t))` (1-based positions `j`, as in (1), (2), (4)–(7) of the
proof of Theorem 4(d), p. 20–21): the sum over the 0-based positions `i ≥ t` of
`v (π i) * (posCompletion p π (i+1) − posCompletion p π t)`, in `ℤ`. With `v = w` it is the
left side of (1), with `v = p` the first term of (1), and with `v ≡ 1` the second. -/
def tailWeighted {n : ℕ} (p v : Fin n → ℕ) (π : Equiv.Perm (Fin n)) (t : ℕ) : ℤ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin n => t ≤ i.val),
    (v (π i) : ℤ) * ((posCompletion p π (i.val + 1) : ℤ) - posCompletion p π t)

end SchedComplexity.Tardiness
