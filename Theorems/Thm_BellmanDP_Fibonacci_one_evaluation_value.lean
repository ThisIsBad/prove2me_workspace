import Mathlib
import Definitions.Def_BellmanDP_Fibonacci_SearchModel

namespace BellmanDP.Fibonacci

/-- Bellman, Ch. I, § 22, proof of Theorem 11, p. 34: "the value of `F₁` is determined by the
process": with one evaluation, `Sup L₁ = 1 = F₁`. -/
theorem one_evaluation_value :
    IsLUB (feasibleLengths 1) (1 : ℝ) := by sorry

end BellmanDP.Fibonacci

