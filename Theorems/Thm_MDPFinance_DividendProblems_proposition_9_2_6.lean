import Mathlib
import Definitions.Def_MDPFinance_DividendProblems_MDM
import Definitions.Def_MDPFinance_DividendProblems_Dividend

open scoped ENNReal NNReal
open MeasureTheory ProbabilityTheory

namespace MDPFinance.DividendProblems

/-- Proposition 9.2.6 (Bäuerle–Rieder, p. 276, PDF 286). `\xi := \sup\{x \in \mathbb N_0 \mid
f^*(x) = 0\}` is finite and `f^*(x) = x - \xi` for all `x \ge \xi`. The set contains `0`
(`D(0) = \{0\}`), so "`\xi < \infty`" says it has a maximum `n`: `f^*(n) = 0` and every `x` with
`f^*(x) = 0` satisfies `x \le n`. -/
theorem proposition_9_2_6 (M : DividendModel) (fstar : ℤ → ℕ) (hfstar : M.IsLargestMaximizer fstar) :
    ∃ n : ℕ, fstar (n : ℤ) = 0 ∧ (∀ x : ℕ, fstar (x : ℤ) = 0 → x ≤ n) ∧
      ∀ x : ℤ, (n : ℤ) ≤ x → fstar x = (x - n).toNat := by sorry

end MDPFinance.DividendProblems

