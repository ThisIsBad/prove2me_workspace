import Mathlib
import Definitions.Def_BellmanDP_Fibonacci_SearchModel

namespace BellmanDP.Fibonacci

/-- Bellman, Ch. I, § 22, Eq. (22.3), pp. 35–36: `F_n ≤ F_{n−1} + F_{n−2}`, in the form the proof
establishes it ("in all cases `L_n < F_{n−1} + F_{n−2}`"): for `n ≥ 2`, every interval length on
which `n` evaluations always locate the maximum within unit length is strictly less than
`F_{n−1} + F_{n−2}`. -/
theorem upper_bound_recursion (n : ℕ) (hn : 2 ≤ n) (L : ℝ) (hL : L ∈ feasibleLengths n) :
    L < (bookFib (n - 1) : ℝ) + bookFib (n - 2) := by sorry

end BellmanDP.Fibonacci

