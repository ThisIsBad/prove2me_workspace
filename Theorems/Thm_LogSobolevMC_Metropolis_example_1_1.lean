import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_LogSobolevMC_Metropolis_Chains

namespace LogSobolevMC.Metropolis

/-- Example 1.1, (1.9), p. 698: the standard Metropolis construction on the nearest-neighbour
walk gives the six-case kernel (1.9) (and `M(x, y) = 0` for `|x − y| ≥ 2`), and
`π(x)M(x, y) = π(y)M(y, x)` for the binomial distribution `π`. -/
theorem example_1_1 (n : ℕ) (hn : 1 ≤ n) :
    MarkovMixing.IsStochastic (binomMetropolis n) ∧
    (∀ x y : Fin (n + 1),
      (((y : ℕ) = (x : ℕ) + 1 ∧ 2 * ((x : ℕ) : ℝ) ≤ (n : ℝ) - 1) ∨
        ((y : ℕ) + 1 = (x : ℕ) ∧ (n : ℝ) + 1 ≤ 2 * ((x : ℕ) : ℝ))) →
      binomMetropolis n x y = 1 / 2) ∧
    (∀ x y : Fin (n + 1),
      (y : ℕ) + 1 = (x : ℕ) → 1 ≤ ((x : ℕ) : ℝ) → 2 * ((x : ℕ) : ℝ) ≤ (n : ℝ) + 1 →
      binomMetropolis n x y = ((x : ℕ) : ℝ) / (2 * ((n : ℝ) - ((x : ℕ) : ℝ) + 1))) ∧
    (∀ x y : Fin (n + 1),
      (y : ℕ) = (x : ℕ) + 1 → (n : ℝ) - 1 ≤ 2 * ((x : ℕ) : ℝ) → ((x : ℕ) : ℝ) ≤ (n : ℝ) - 1 →
      binomMetropolis n x y = ((n : ℝ) - ((x : ℕ) : ℝ)) / (2 * (((x : ℕ) : ℝ) + 1))) ∧
    (∀ x : Fin (n + 1), 2 * ((x : ℕ) : ℝ) ≤ (n : ℝ) - 1 →
      binomMetropolis n x x =
        ((n : ℝ) - 2 * ((x : ℕ) : ℝ) + 1) / (2 * ((n : ℝ) - ((x : ℕ) : ℝ) + 1))) ∧
    (∀ x : Fin (n + 1), (n : ℝ) + 1 ≤ 2 * ((x : ℕ) : ℝ) →
      binomMetropolis n x x =
        (2 * ((x : ℕ) : ℝ) - (n : ℝ) + 1) / (2 * (((x : ℕ) : ℝ) + 1))) ∧
    (∀ x : Fin (n + 1), 2 * (x : ℕ) = n →
      binomMetropolis n x x = 2 / ((n : ℝ) + 2)) ∧
    (∀ x y : Fin (n + 1), x ≠ y → (y : ℕ) ≠ (x : ℕ) + 1 → (y : ℕ) + 1 ≠ (x : ℕ) →
      binomMetropolis n x y = 0) ∧
    MarkovMixing.DetailedBalance (binomMetropolis n) (binomPi n) := by sorry

end LogSobolevMC.Metropolis

