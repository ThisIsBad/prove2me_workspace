import Mathlib
import Definitions.Def_BellmanDP_Fibonacci_SearchModel

namespace BellmanDP.Fibonacci

/-- Bellman, Ch. I, § 22, proof of Theorem 11, p. 36: choosing `L_n`, `x₁`, `x₂` arbitrarily close
to their upper bounds gives `F_n = F_{n−1} + F_{n−2}`: for `n ≥ 2`, every length
`0 < L < F_{n−1} + F_{n−2}` admits a procedure that always locates the maximum within unit length
using at most `n` evaluations. -/
theorem lengths_below_attainable (n : ℕ) (hn : 2 ≤ n) (L : ℝ) (hL0 : 0 < L)
    (hL : L < (bookFib (n - 1) : ℝ) + bookFib (n - 2)) :
    L ∈ feasibleLengths n := by sorry

end BellmanDP.Fibonacci

