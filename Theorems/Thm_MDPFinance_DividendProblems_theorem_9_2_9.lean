import Mathlib
import Definitions.Def_MDPFinance_DividendProblems_MDM
import Definitions.Def_MDPFinance_DividendProblems_Dividend
import Definitions.Def_MDPFinance_DividendProblems_BandPolicy

open scoped ENNReal NNReal
open MeasureTheory ProbabilityTheory

namespace MDPFinance.DividendProblems

/-- Theorem 9.2.9 (Bäuerle–Rieder, p. 278, PDF 288). The stationary policy `(f^*,f^*,\dots)`,
`f^*` the largest maximizer of `J_\infty`, is optimal (`J_{\infty (f^*)^\infty} = J_\infty`) and
is a band-policy (Definition 9.2.5, on the nonnegative states; `f^*(x) = 0` for `x < 0` is
forced by `D(x) = \{0\}`). -/
theorem theorem_9_2_9 (M : DividendModel) (fstar : ℤ → ℕ) (hfstar : M.IsLargestMaximizer fstar) :
    (∀ x : ℤ, Jinfpi M.toMDM (fun _ => fstar) x = M.Jinf x) ∧
      IsBandPolicy (fun x : ℕ => fstar (x : ℤ)) := by sorry

end MDPFinance.DividendProblems

