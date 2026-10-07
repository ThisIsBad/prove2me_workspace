import Mathlib
import Definitions.Def_BellmanDP_Fibonacci_SearchModel

namespace BellmanDP.Fibonacci

/-- Bellman, Ch. I, § 22, proof of Theorem 11, p. 35: for `n = 2`, `L₂ = 2 − ε` is attainable
(`x₁ = 1 − ε`, `x₂ = 1`) for arbitrarily small `ε > 0`, and `F₂ = 2 = F₁ + F₀`. -/
theorem two_evaluations_value :
    IsLUB (feasibleLengths 2) (2 : ℝ) := by sorry

end BellmanDP.Fibonacci

