import Mathlib
import Definitions.Def_BeckTeboulleMD_EMDA_Setting

namespace BeckTeboulleMD.EMDA

/-- Remark 5.1, p. 174: the strong convexity inequality of Proposition 5.1(a) remains true on the
whole simplex `Δ` (with `0 ln 0 = 0`): (i) `∑_j (x_j − y_j) ln(x_j / y_j) ≥ ‖x − y‖₁²` for `x, y ∈ Δ`
with the same support (otherwise the left side is `+∞` on the page); (ii) `ψ_e` is `1`-strongly
convex on `Δ` with respect to `‖·‖₁`. -/
theorem remark_5_1 {n : ℕ} :
    (∀ x ∈ stdSimplex ℝ (Fin n), ∀ y ∈ stdSimplex ℝ (Fin n), (∀ j, x j = 0 ↔ y j = 0) →
      (∑ j, |x j - y j|) ^ 2 ≤ ∑ j, (x j - y j) * Real.log (x j / y j)) ∧
    (∀ x ∈ stdSimplex ℝ (Fin n), ∀ y ∈ stdSimplex ℝ (Fin n), ∀ a b : ℝ,
      0 ≤ a → 0 ≤ b → a + b = 1 →
      entropy (a • x + b • y)
        ≤ a * entropy x + b * entropy y - a * b * (1 / 2 * (∑ j, |x j - y j|) ^ 2)) := by sorry

end BeckTeboulleMD.EMDA

