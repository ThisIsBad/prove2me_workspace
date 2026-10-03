import Mathlib
import Definitions.Def_MDPFinance_StoppingFinance_CreditModel

open MeasureTheory

namespace MDPFinance.StoppingFinance

/-- **Theorem 11.2.1** (pp. 340-341). Under the structural assumptions: a) `J_n(x)` is increasing
in `x` and in `n`; b) there are thresholds `x_N^* ≤ … ≤ x_1^*` (in `[-∞,∞]`, `inf ∅ = ∞`) such
that the cancellation set with `n` periods left is `S_n^* = {x ∈ E | x < x_n^*}` — the states where
extending, `c̄_n(x) = c(x) + β ∫ J_{n−1} dQ^X(·|x)`, is worse than cancelling — and the policy
`f_n^* := 1_{S_n^*}` is optimal: `f_n^*` is a maximizer of `J_{n-1}` (`T_{f_n^*} J_{n−1} = J_n`). -/
theorem theorem_11_2_1 (M : CreditModel) (hM : M.StructuralAssumptions) (N : ℕ) :
    (∀ n : ℕ, Monotone (M.J n)) ∧
    (∀ (m n : ℕ), m ≤ n → ∀ x : ℝ, M.J m x ≤ M.J n x) ∧
    (∃ xstar : ℕ → EReal,
      (∀ (m n : ℕ), 1 ≤ m → m ≤ n → n ≤ N → xstar n ≤ xstar m) ∧
      (∀ (n : ℕ) (x : ℝ), 1 ≤ n → n ≤ N → (M.cbar n x < 0 ↔ (x : EReal) < xstar n)) ∧
      ∀ (n : ℕ) (x : ℝ), 1 ≤ n → n ≤ N →
        (if (x : EReal) < xstar n then 0 else M.cbar n x) = M.J n x) := by sorry

end MDPFinance.StoppingFinance
