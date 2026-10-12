import Mathlib

namespace Timetabling85.ClassTeacher

/-- `lo s p = ⌊s / p⌋`, the largest integer not larger than `s / p` (de Werra 1985, p. 153).
The division is in `ℚ`; for `p = 0` Lean's convention gives `s / 0 = 0`. -/
def lo (s p : ℕ) : ℕ := ⌊(s : ℚ) / (p : ℚ)⌋₊

/-- `hi s p = ⌈s / p⌉`, the smallest integer not less than `s / p` (de Werra 1985, p. 153).
The division is in `ℚ`; for `p = 0` Lean's convention gives `s / 0 = 0`. -/
def hi (s p : ℕ) : ℕ := ⌈(s : ℚ) / (p : ℚ)⌉₊

/-- Row sum `∑_{j=1}^n r_ij` of the requirement matrix: all lectures of class `c_i`. -/
def rowSum {m n : ℕ} (R : Fin m → Fin n → ℕ) (i : Fin m) : ℕ := ∑ j, R i j

/-- Column sum `∑_{i=1}^m r_ij` of the requirement matrix: all lectures of teacher `t_j`. -/
def colSum {m n : ℕ} (R : Fin m → Fin n → ℕ) (j : Fin n) : ℕ := ∑ i, R i j

/-- Constraint (1): every lecture is scheduled exactly once,
`∑_{k=1}^p x_ijk = r_ij` for all classes `i` and teachers `j`. -/
def SchedulesAll {m n : ℕ} (R : Fin m → Fin n → ℕ) (p : ℕ)
    (x : Fin m → Fin n → Fin p → ℕ) : Prop :=
  ∀ i j, ∑ k, x i j k = R i j

/-- Problem CT1 (p. 152): constraints (1)–(4). `x i j k` is `1` if class `c_i` and teacher `t_j`
meet at period `k` and `0` otherwise. -/
def IsCT1 {m n : ℕ} (R : Fin m → Fin n → ℕ) (p : ℕ)
    (x : Fin m → Fin n → Fin p → ℕ) : Prop :=
  SchedulesAll R p x ∧
  (∀ i k, ∑ j, x i j k ≤ 1) ∧          -- (2)
  (∀ j k, ∑ i, x i j k ≤ 1) ∧          -- (3)
  (∀ i j k, x i j k ≤ 1)               -- (4): x_ijk ∈ {0, 1}

/-- Problem CT2 (p. 152): constraints (1), (5), (6), (7). `x i j k` is the number of lectures
of class `c_i` with teacher `t_j` assigned to day `k`; (7) (`x_ijk ≥ 0` integer) is the type `ℕ`.
`a i` (resp. `b j`) is the maximum daily number of lectures of class `c_i` (resp. teacher `t_j`). -/
def IsCT2 {m n : ℕ} (R : Fin m → Fin n → ℕ) (p : ℕ) (a : Fin m → ℕ) (b : Fin n → ℕ)
    (x : Fin m → Fin n → Fin p → ℕ) : Prop :=
  SchedulesAll R p x ∧
  (∀ i k, ∑ j, x i j k ≤ a i) ∧        -- (5)
  (∀ j k, ∑ i, x i j k ≤ b j)          -- (6)

/-- Problem CT3 (p. 153): constraints (1), (8), (9), (10). The bounds in (8) and (9) are the
floor and ceiling of the row (resp. column) **total** divided by `p`. -/
def IsCT3 {m n : ℕ} (R : Fin m → Fin n → ℕ) (p : ℕ)
    (x : Fin m → Fin n → Fin p → ℕ) : Prop :=
  SchedulesAll R p x ∧
  (∀ i k, lo (rowSum R i) p ≤ ∑ j, x i j k ∧ ∑ j, x i j k ≤ hi (rowSum R i) p) ∧   -- (8)
  (∀ j k, lo (colSum R j) p ≤ ∑ i, x i j k ∧ ∑ i, x i j k ≤ hi (colSum R j) p) ∧   -- (9)
  (∀ i j k, lo (R i j) p ≤ x i j k ∧ x i j k ≤ hi (R i j) p)                       -- (10)

/-- The minimum number of days of the display on p. 153:
`max (max_j ⌈∑_i r_ij / b_j⌉, max_i ⌈∑_j r_ij / a_i⌉)`; an empty maximum is `0`. -/
def minDays {m n : ℕ} (R : Fin m → Fin n → ℕ) (a : Fin m → ℕ) (b : Fin n → ℕ) : ℕ :=
  max (Finset.univ.sup fun j => hi (colSum R j) (b j))
      (Finset.univ.sup fun i => hi (rowSum R i) (a i))

end Timetabling85.ClassTeacher
