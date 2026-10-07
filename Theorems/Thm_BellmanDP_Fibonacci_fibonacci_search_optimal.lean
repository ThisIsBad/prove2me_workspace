import Mathlib
import Definitions.Def_BellmanDP_Fibonacci_SearchModel

namespace BellmanDP.Fibonacci

/-- Bellman, *Dynamic Programming*, Ch. I, § 22, Theorem 11, p. 34: `F_n = Sup L_n` is the `n`th
Fibonacci number (`F₀ = F₁ = 1`, `F_n = F_{n−1} + F_{n−2}` for `n ≥ 2`): for every `n`, the least
upper bound of the lengths `L` of intervals `[0, L]` on which `n` adaptively chosen evaluations
always locate the maximum of a strictly unimodal function within a sub-interval of unit length is
`bookFib n`. -/
theorem fibonacci_search_optimal (n : ℕ) :
    IsLUB (feasibleLengths n) (bookFib n : ℝ) := by sorry

end BellmanDP.Fibonacci

