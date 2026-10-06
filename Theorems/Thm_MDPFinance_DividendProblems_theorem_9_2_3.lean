import Mathlib
import Definitions.Def_MDPFinance_DividendProblems_MDM
import Definitions.Def_MDPFinance_DividendProblems_Dividend

open scoped ENNReal NNReal
open MeasureTheory ProbabilityTheory

namespace MDPFinance.DividendProblems

/-- Theorem 9.2.3 (Bäuerle–Rieder, p. 274, PDF 284). a) `x + \beta\mathbb EZ^+/(1-\beta q^+) \le
J_\infty(x) \le x + \beta\mathbb EZ^+/(1-\beta)` for `x \ge 0`. b) `J_\infty` is increasing and
`J_\infty(x) - J_\infty(y) \ge x - y` for `x \ge y \ge 0`. c) `f^*(x - f^*(x)) = 0` and
`J_\infty(x) - f^*(x) = J_\infty(x - f^*(x))` for `x \ge 0`, `f^*` the largest maximizer of
`J_\infty`. Stated in `[0,\infty]` (`J_\infty` is finite by Lemma 9.2.2). -/
theorem theorem_9_2_3 (M : DividendModel) (fstar : ℤ → ℕ) (hfstar : M.IsLargestMaximizer fstar) :
    (∀ x : ℤ, 0 ≤ x →
        ENNReal.ofReal ((x : ℝ) + M.β * M.EZplus / (1 - M.β * M.qplus)) ≤ M.Jinf x ∧
          M.Jinf x ≤ ENNReal.ofReal ((x : ℝ) + M.β * M.EZplus / (1 - M.β))) ∧
      (Monotone M.Jinf ∧
        ∀ x y : ℤ, 0 ≤ y → y ≤ x → M.Jinf y + ((x - y).toNat : ℝ≥0∞) ≤ M.Jinf x) ∧
      (∀ x : ℤ, 0 ≤ x → fstar (x - (fstar x : ℤ)) = 0 ∧
        M.Jinf x = (fstar x : ℝ≥0∞) + M.Jinf (x - (fstar x : ℤ))) := by sorry

end MDPFinance.DividendProblems

