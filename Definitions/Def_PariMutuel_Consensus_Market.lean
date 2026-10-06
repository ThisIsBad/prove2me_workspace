import Mathlib

namespace PariMutuel.Consensus

/-- A pari-mutuel market (Eisenberg–Gale 1959, pp. 165–166): `m` bettors `B_i` (indexed by `Fin m`)
and `n` horses `H_j` (indexed by `Fin n`; the paper indexes from 1, Lean from 0).
`P i j` is bettor `i`'s subjective probability that horse `j` wins, `b i` is bettor `i`'s budget.
Every standing assumption of the paper is a field: each row of `P` is a probability distribution
(p. 165, "subjective probability distribution"), each column of `P` has a positive entry (p. 166),
each budget is positive (p. 165), and the budgets sum to one (p. 166). -/
structure Market (m n : ℕ) where
  /-- The subjective probability matrix `P = (p_ij)`. -/
  P : Fin m → Fin n → ℝ
  /-- The budgets `b_i`. -/
  b : Fin m → ℝ
  P_nonneg : ∀ i j, 0 ≤ P i j
  P_row_sum : ∀ i, ∑ j, P i j = 1
  P_col_pos : ∀ j, ∃ i, 0 < P i j
  b_pos : ∀ i, 0 < b i
  b_sum : ∑ i, b i = 1

namespace Market

variable {m n : ℕ}

/-- There is at least one bettor, since the budgets sum to one. -/
theorem univ_nonempty (M : Market m n) : (Finset.univ : Finset (Fin m)).Nonempty := by
  rcases (Finset.univ : Finset (Fin m)).eq_empty_or_nonempty with h | h
  · have hs := M.b_sum
    rw [h, Finset.sum_empty] at hs
    norm_num at hs
  · exact h

/-- Equilibrium probabilities and bets (p. 166): nonnegative numbers `π j` and `β i j` satisfying
(1) the budget relation `∑_j β_ij = b_i`, (2) the pari-mutuel condition `∑_i β_ij = π_j`, and
(3) "if `μ_i = max_s p_is/π_s` and `β_ij > 0`, then `μ_i = p_ij/π_j`", written multiplied out:
whenever `β_ij > 0`, `p_is π_j ≤ p_ij π_s` for every horse `s`. This is the paper's (3) when all
`π_s > 0`, and its reading `p_is/0 = +∞` when some `π_s = 0`. Positivity of `π` is not assumed. -/
def IsEquilibrium (M : Market m n) (π : Fin n → ℝ) (β : Fin m → Fin n → ℝ) : Prop :=
  (∀ j, 0 ≤ π j) ∧ (∀ i j, 0 ≤ β i j) ∧
  (∀ i, ∑ j, β i j = M.b i) ∧
  (∀ j, ∑ i, β i j = π j) ∧
  (∀ i j, 0 < β i j → ∀ s, M.P i s * π j ≤ M.P i j * π s)

end Market

end PariMutuel.Consensus
