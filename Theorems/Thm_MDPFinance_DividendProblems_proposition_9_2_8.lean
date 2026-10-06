import Mathlib
import Definitions.Def_MDPFinance_DividendProblems_MDM
import Definitions.Def_MDPFinance_DividendProblems_Dividend

open scoped ENNReal NNReal
open MeasureTheory ProbabilityTheory

namespace MDPFinance.DividendProblems

/-- Proposition 9.2.8 (Bäuerle–Rieder, p. 277, PDF 287). Let `x_0 \ge 0`. If `f^*(x_0) = a_0` and
`f^*(x_0+1) > 0`, then `f^*(x_0+1) = a_0 + 1`. -/
theorem proposition_9_2_8 (M : DividendModel) (fstar : ℤ → ℕ) (hfstar : M.IsLargestMaximizer fstar)
    (x0 : ℤ) (hx0 : 0 ≤ x0) (a0 : ℕ) (ha0 : fstar x0 = a0) (hpos : 0 < fstar (x0 + 1)) :
    fstar (x0 + 1) = a0 + 1 := by sorry

end MDPFinance.DividendProblems

