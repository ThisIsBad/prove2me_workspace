import Mathlib
import Definitions.Def_BeckTeboulleMD_EMDA_Setting

namespace BeckTeboulleMD.EMDA

/-- Proposition 5.1(a), p. 173: on the relative interior of the unit simplex,
`⟨∇ψ_e(x) − ∇ψ_e(y), x − y⟩ = ∑_j (x_j − y_j) ln(x_j / y_j) ≥ ‖x − y‖₁²`,
and `ψ_e` is `1`-strongly convex there with respect to `‖·‖₁`. -/
theorem proposition_5_1_a {n : ℕ} :
    (∀ x ∈ relIntSimplex n, ∀ y ∈ relIntSimplex n,
      (fderiv ℝ (entropy (n := n)) x - fderiv ℝ (entropy (n := n)) y) (x - y)
        = ∑ j, (x j - y j) * Real.log (x j / y j)) ∧
    (∀ x ∈ relIntSimplex n, ∀ y ∈ relIntSimplex n,
      (∑ j, |x j - y j|) ^ 2 ≤ ∑ j, (x j - y j) * Real.log (x j / y j)) ∧
    (∀ x ∈ relIntSimplex n, ∀ y ∈ relIntSimplex n, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      entropy (a • x + b • y)
        ≤ a * entropy x + b * entropy y - a * b * (1 / 2 * (∑ j, |x j - y j|) ^ 2)) := by sorry

end BeckTeboulleMD.EMDA

