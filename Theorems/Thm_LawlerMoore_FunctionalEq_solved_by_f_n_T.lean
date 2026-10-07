import Mathlib
import Definitions.Def_LawlerMoore_FunctionalEq_Problem
import Definitions.Def_LawlerMoore_FunctionalEq_Recursion

namespace LawlerMoore.FunctionalEq

/-- Section 1, p. 77 (after Eq. (1)): if every loss function `α_j`, `β_j` is monotone
nondecreasing in the completion time, then the problem is solved by `f(n, T)` with
`T = ∑_{j=1}^n max {a_j, b_j}`: `f(n, T)` is finite, it is at most the total loss of every
mode assignment with every feasible timing of all `n` jobs (no deadline), and some mode
assignment with some feasible timing attains it. -/
theorem solved_by_f_n_T {n : ℕ} (a b : Fin n → ℕ) (α β : Fin n → ℕ → ℝ)
    (hα : ∀ j, Monotone (α j)) (hβ : ∀ j, Monotone (β j)) :
    f a b α β n ((∑ j, max (a j) (b j) : ℕ) : ℤ) ≠ ⊤ ∧
      (∀ (m : Fin n → Bool) (c : Fin n → ℕ), IsFeasible a b m c n →
        f a b α β n ((∑ j, max (a j) (b j) : ℕ) : ℤ) ≤ ((totalLoss α β m c n : ℝ) : WithTop ℝ)) ∧
      ∃ (m : Fin n → Bool) (c : Fin n → ℕ), IsFeasible a b m c n ∧
        ((totalLoss α β m c n : ℝ) : WithTop ℝ) = f a b α β n ((∑ j, max (a j) (b j) : ℕ) : ℤ) := by sorry

end LawlerMoore.FunctionalEq

