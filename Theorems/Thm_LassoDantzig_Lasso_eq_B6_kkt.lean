import Mathlib
import Definitions.Def_LassoDantzig_Lasso_Model

open MeasureTheory ProbabilityTheory

namespace LassoDantzig.Lasso

/-- (B.6), p. 22, for the Lasso (7.2): for `r > 0`, `β̂` is a Lasso solution if and only if,
for every `j`, `(1/n) x_{(j)}ᵀ(y − Xβ̂) = r sign(β̂ⱼ)` when `β̂ⱼ ≠ 0` and
`|(1/n) x_{(j)}ᵀ(y − Xβ̂)| ≤ r` when `β̂ⱼ = 0`, where `x_{(j)}` is the `j`-th column of `X`. -/
theorem eq_B6_kkt {n M : ℕ} (hn : 1 ≤ n)
    (X : Matrix (Fin n) (Fin M) ℝ) (y : Fin n → ℝ) (r : ℝ) (hr : 0 < r)
    (βhat : Fin M → ℝ) :
    IsLasso X y r βhat ↔
      ∀ j : Fin M,
        (βhat j ≠ 0 →
          (1 / (n : ℝ)) * ∑ i, X i j * (y i - X.mulVec βhat i) = r * Real.sign (βhat j)) ∧
        (βhat j = 0 →
          |(1 / (n : ℝ)) * ∑ i, X i j * (y i - X.mulVec βhat i)| ≤ r) := by sorry

end LassoDantzig.Lasso
