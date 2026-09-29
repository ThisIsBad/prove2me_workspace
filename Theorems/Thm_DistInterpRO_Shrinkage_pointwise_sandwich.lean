import Mathlib
import Definitions.Def_DistInterpRO_Shrinkage_Model

open MeasureTheory
open scoped Pointwise

namespace DistInterpRO.Shrinkage

/-- §4.2, proof of Theorem 4.1 (p. 105), display after "Thus,": for `x₁ ∈ Δ` and
`x′₁ = αx₁`,
`(1 − α)f(v, x₀) + αf(v, x₀ + x₁) − αD²h ≤ f(v, x₀ + x′₁)
  ≤ (1 − α)f(v, x₀) + αf(v, x₀ + x₁) + αD²h`. -/
theorem pointwise_sandwich {m : ℕ} {V : Type*} (f : V → EuclideanSpace ℝ (Fin m) → ℝ) (v : V)
    (x₀ : EuclideanSpace ℝ (Fin m)) (Δ : Set (EuclideanSpace ℝ (Fin m))) (hΔc : IsCompact Δ)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (h : ℝ) (hh : 0 ≤ h) (hf : HasBoundedHessian (f v) h)
    (x₁ : EuclideanSpace ℝ (Fin m)) (hx₁ : x₁ ∈ Δ) :
    (1 - α) * f v x₀ + α * f v (x₀ + x₁) - α * devRadius Δ ^ 2 * h ≤ f v (x₀ + α • x₁) ∧
      f v (x₀ + α • x₁) ≤ (1 - α) * f v x₀ + α * f v (x₀ + x₁) + α * devRadius Δ ^ 2 * h := by sorry

end DistInterpRO.Shrinkage
