import Mathlib
import Definitions.Def_MDPFinance_DividendProblems_MDM
import Definitions.Def_MDPFinance_DividendProblems_Dividend

open scoped ENNReal NNReal
open MeasureTheory ProbabilityTheory

namespace MDPFinance.DividendProblems

/-- Corollary 9.2.4 (Bäuerle–Rieder, p. 275, PDF 285). a) If `\mathbb P(Z \le 0) = 1` then
`J_\infty(x) = x^+` and `f^*(x) = x^+`. b) If `\mathbb P(Z \ge 0) = 1` then `J_\infty(x) = x +
\beta\mathbb EZ/(1-\beta)` for `x \ge 0` and `f^*(x) = x^+`. -/
theorem corollary_9_2_4 (M : DividendModel) (fstar : ℤ → ℕ) (hfstar : M.IsLargestMaximizer fstar) :
    (M.Zpmf.toMeasure {k : ℤ | k ≤ 0} = 1 →
        (∀ x : ℤ, M.Jinf x = ((max x 0).toNat : ℝ≥0∞)) ∧ ∀ x : ℤ, (fstar x : ℤ) = max x 0) ∧
      (M.Zpmf.toMeasure {k : ℤ | 0 ≤ k} = 1 →
        (∀ x : ℤ, 0 ≤ x → M.Jinf x = ENNReal.ofReal ((x : ℝ) + M.β * M.EZ / (1 - M.β))) ∧
          ∀ x : ℤ, (fstar x : ℤ) = max x 0) := by sorry

end MDPFinance.DividendProblems
