import Mathlib

namespace ManneJobShop.Formulation

/-- A job-shop instance in the sense of Manne (1960), pp. 219–221. There are `n` tasks, indexed
`0, …, n-1` (the paper's task `j` is index `j - 1`). Task `j` needs the single machine `mach j` for
`a j` consecutive days. `T` is the horizon: start days range over `0, 1, …, T` (p. 219).
`(j, k) ∈ prec` imposes (5a) `x_j + a_j ≤ x_k`; `(j, k) ∈ delay` imposes (5c)
`x_j + a_j + Θ_jk = x_k`; `due j = some d` imposes the delivery date (6) `x_j + a_j ≤ d`. -/
structure Instance (n : ℕ) where
  /-- number of machines -/
  M : ℕ
  /-- the single machine each task requires -/
  mach : Fin n → Fin M
  /-- durations `a_j` (integral numbers of days) -/
  a : Fin n → ℤ
  /-- the horizon `T`: start days lie in `{0, …, T}` -/
  T : ℤ
  /-- precedence pairs for (5a): `(j, k) ∈ prec` means job `j` precedes job `k` -/
  prec : Finset (Fin n × Fin n)
  /-- pairs carrying an exact delay, condition (5c) -/
  delay : Finset (Fin n × Fin n)
  /-- the exact delays `Θ_jk` of (5c), read on `delay` only -/
  Θ : Fin n → Fin n → ℤ
  /-- delivery dates `d_j` of (6), where present -/
  due : Fin n → Option ℤ

variable {n : ℕ}

/-- The conflicting pairs of machine assignments (p. 222): pairs `(j, k)` with `j < k` whose tasks
use the same machine. Each carries one 0–1 variable `y_jk`. -/
def conflicts (I : Instance n) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2 ∧ I.mach p.1 = I.mach p.2)

/-- A schedule: integer start days `x_j ∈ {0, …, T}` (p. 219) satisfying the noninterference
condition (1) on every conflicting pair, precedence (5a), exact delays (5c) and delivery
dates (6). -/
def IsSchedule (I : Instance n) (x : Fin n → ℤ) : Prop :=
  (∀ j, 0 ≤ x j ∧ x j ≤ I.T) ∧
  (∀ p ∈ conflicts I, x p.1 - x p.2 ≥ I.a p.2 ∨ x p.2 - x p.1 ≥ I.a p.1) ∧
  (∀ p ∈ I.prec, x p.1 + I.a p.1 ≤ x p.2) ∧
  (∀ p ∈ I.delay, x p.1 + I.a p.1 + I.Θ p.1 p.2 = x p.2) ∧
  (∀ j d, I.due j = some d → x j + I.a j ≤ d)

/-- The make-span of a schedule, `max_j (x_j + a_j)`: the elapsed calendar time for the
performance of all jobs when the shop starts on day 0 (p. 219). Needs at least one task. -/
def makespan [NeZero n] (I : Instance n) (x : Fin n → ℤ) : ℤ :=
  Finset.univ.sup' Finset.univ_nonempty (fun j => x j + I.a j)

/-- Manne's integer program (2)–(7), p. 221: integer start days `0 ≤ x_j ≤ T`, integer `y_jk` on
every conflicting pair with (2) `0 ≤ y_jk ≤ 1`, (3) `(T + a_k) y_jk + (x_j - x_k) ≥ a_k`,
(4) `(T + a_j)(1 - y_jk) + (x_k - x_j) ≥ a_j`, together with (5a), (5c), (6) and
(7) `x_j + a_j ≤ t` for every task. `y` is read on conflicting pairs only. -/
def IsIPFeasible (I : Instance n) (x : Fin n → ℤ) (y : Fin n → Fin n → ℤ) (t : ℤ) : Prop :=
  (∀ j, 0 ≤ x j ∧ x j ≤ I.T) ∧
  (∀ p ∈ conflicts I,
    (0 ≤ y p.1 p.2 ∧ y p.1 p.2 ≤ 1) ∧
    (I.T + I.a p.2) * y p.1 p.2 + (x p.1 - x p.2) ≥ I.a p.2 ∧
    (I.T + I.a p.1) * (1 - y p.1 p.2) + (x p.2 - x p.1) ≥ I.a p.1) ∧
  (∀ p ∈ I.prec, x p.1 + I.a p.1 ≤ x p.2) ∧
  (∀ p ∈ I.delay, x p.1 + I.a p.1 + I.Θ p.1 p.2 = x p.2) ∧
  (∀ j d, I.due j = some d → x j + I.a j ≤ d) ∧
  (∀ j, x j + I.a j ≤ t)

end ManneJobShop.Formulation
