import Mathlib
import Definitions.Def_BellmanDP_Fibonacci_SearchModel

namespace BellmanDP.Fibonacci

open Filter Topology

/-- Bellman, Ch. I, § 22, Eqs. (22.5)–(22.6), p. 36: with `r₁ = (1 + √5)/2` and `r₂ = (1 − √5)/2`,
`F_n = ((r₂ − 1)/(r₂ − r₁)) r₁ⁿ + ((1 − r₁)/(r₂ − r₁)) r₂ⁿ` for every `n`; and
`F_{n+1}/F_n → r₁` as `n → ∞`. -/
theorem binet_formula :
    (∀ n : ℕ, (bookFib n : ℝ) =
      ((1 - Real.sqrt 5) / 2 - 1) / ((1 - Real.sqrt 5) / 2 - (1 + Real.sqrt 5) / 2) *
          ((1 + Real.sqrt 5) / 2) ^ n +
        (1 - (1 + Real.sqrt 5) / 2) / ((1 - Real.sqrt 5) / 2 - (1 + Real.sqrt 5) / 2) *
          ((1 - Real.sqrt 5) / 2) ^ n) ∧
    Tendsto (fun n : ℕ => (bookFib (n + 1) : ℝ) / bookFib n) atTop
      (𝓝 ((1 + Real.sqrt 5) / 2)) := by sorry

end BellmanDP.Fibonacci

