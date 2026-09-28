import Definitions.Def_Nullstellensatz_Defs
import Mathlib

open MvPolynomial

namespace Nullstellensatz

theorem real_counterexample :
    Ideal.span {(Polynomial.X ^ 2 + 1 : Polynomial ℝ)} ≠ ⊤ ∧
      ¬ ∃ x : ℝ, ∀ f ∈ Ideal.span {(Polynomial.X ^ 2 + 1 : Polynomial ℝ)}, f.eval x = 0 := by
  sorry

end Nullstellensatz
