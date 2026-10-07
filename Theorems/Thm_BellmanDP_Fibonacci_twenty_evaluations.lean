import Mathlib
import Definitions.Def_BellmanDP_Fibonacci_SearchModel

namespace BellmanDP.Fibonacci

/-- Bellman, Ch. I, § 22, after Eq. (22.4), p. 36: `F₂₀ > 10,000`; hence the maximum of a strictly
unimodal function on an interval of any length `L > 0` can always be located within `10⁻⁴ L` with
at most 20 calculations of the value of the function. -/
theorem twenty_evaluations :
    10000 < bookFib 20 ∧
    ∀ L : ℝ, 0 < L → ∃ T : SearchTree ℝ (ℝ × ℝ), Locates T L (L / 10 ^ 4) 20 := by sorry

end BellmanDP.Fibonacci

