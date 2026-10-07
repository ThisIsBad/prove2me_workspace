import Mathlib
import Definitions.Def_BellmanDP_Fibonacci_SearchModel

namespace BellmanDP.Fibonacci

/-- Bellman, Ch. I, § 22, Theorem 12, p. 36, **corrected**. The book prints `K₀ = 1, K₁ = 1,
K₂ = 2, K₃ = 4` and `K_n = 1 + F_n` for `n ≥ 3`; the latter is false from `n = 4` on (seven
points can be searched with four evaluations, while `1 + F₄ = 6`). The corrected statement keeps
the printed initial values and replaces (7) by `K_n = F_{n+1} − 1` for `n ≥ 3` (which agrees with
the printed value at `n = 3`). Here `K_n` is the greatest number of points on which the maximum
of every strictly unimodal function can always be identified in `n` computations. -/
theorem discrete_search_corrected :
    IsGreatest (identifiableSizes 0) 1 ∧
    IsGreatest (identifiableSizes 1) 1 ∧
    IsGreatest (identifiableSizes 2) 2 ∧
    IsGreatest (identifiableSizes 3) 4 ∧
    ∀ n : ℕ, 3 ≤ n → IsGreatest (identifiableSizes n) (bookFib (n + 1) - 1) := by sorry

end BellmanDP.Fibonacci

