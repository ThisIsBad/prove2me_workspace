import Mathlib

namespace ManneLP.Equilibrium

/-- Manne's single-item inventory model (Manne 1960, §2–§3, pp. 260–261).

* `T` is the positive integer upper limit on inventory accumulation; stock levels are
  `0, 1, …, T`.
* `A` is the finite set of admissible pairs `(i, j)` (initial stock `i`, production `j`) that
  carry an unknown `xᵢⱼ`. Every admissible pair has available stock `k = i + j ≤ T`, so the
  terminal stock `max(0, k − n)` never exceeds `T`; producing nothing is admissible at every
  stock level `i ≤ T`.
* `p n` is the probability that `n` units are demanded in a month (serially independent).
* `C₁ i`, `C₂ j`, `C₃ m` are the costs attached to the initial stock `i`, the production
  quantity `j` and the shortage level `m = n − k` (an integer, negative when demand is below the
  available stock). No convexity, sign or monotonicity is assumed. -/
structure Model where
  T : ℕ
  T_pos : 0 < T
  A : Finset (ℕ × ℕ)
  A_le : ∀ a ∈ A, a.1 + a.2 ≤ T
  zero_mem : ∀ i, i ≤ T → (i, 0) ∈ A
  p : ℕ → ℝ
  p_nonneg : ∀ n, 0 ≤ p n
  p_hasSum : HasSum p 1
  C₁ : ℕ → ℝ
  C₂ : ℕ → ℝ
  C₃ : ℤ → ℝ

/-- The stock levels `0, 1, …, T`. -/
def states (M : Model) : Finset ℕ := Finset.range (M.T + 1)

/-- The production quantities admissible at initial stock `i`: those `j` with `(i, j) ∈ A`. -/
def actions (M : Model) (i : ℕ) : Finset ℕ :=
  (Finset.range (M.T + 1)).filter (fun j => (i, j) ∈ M.A)

/-- The probability that the month-end stock `max(0, k − n)` equals `t` when the available stock
is `k` and the demand `n` has law `p`. In `ℕ`, truncated subtraction `k - n` is exactly
`max(0, k − n)`. -/
noncomputable def termProb (M : Model) (k t : ℕ) : ℝ :=
  ∑' n : ℕ, if k - n = t then M.p n else 0

end ManneLP.Equilibrium
