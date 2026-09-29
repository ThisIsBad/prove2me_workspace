import Mathlib
import Definitions.Def_DistInterpRO_Shrinkage_Model

open MeasureTheory
open scoped Pointwise

namespace DistInterpRO.Shrinkage

/-- §4.2, proof of Theorem 4.1 (p. 105), display after "Since this holds for all x₁ ∈ Δ":
`(1−α)f(v, x₀) + α min_{x_δ∈Δ} f(v, x₀+x_δ) − αD²h ≤ min_{x′_δ∈αΔ} f(v, x₀+x′_δ)
  ≤ (1−α)f(v, x₀) + α min_{x_δ∈Δ} f(v, x₀+x_δ) + αD²h`.
The minima are written as infima over the compact sets `Δ` and `αΔ`; they are attained. -/
theorem min_sandwich {m : ℕ} {V : Type*} (f : V → EuclideanSpace ℝ (Fin m) → ℝ) (v : V)
    (x₀ : EuclideanSpace ℝ (Fin m)) (Δ : Set (EuclideanSpace ℝ (Fin m))) (hΔc : IsCompact Δ)
    (hΔ0 : (0 : EuclideanSpace ℝ (Fin m)) ∈ Δ)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (h : ℝ) (hh : 0 ≤ h) (hf : HasBoundedHessian (f v) h) :
    (1 - α) * f v x₀ + α * (⨅ x : Δ, f v (x₀ + x)) - α * devRadius Δ ^ 2 * h ≤
        (⨅ x : (α • Δ : Set (EuclideanSpace ℝ (Fin m))), f v (x₀ + x)) ∧
      (⨅ x : (α • Δ : Set (EuclideanSpace ℝ (Fin m))), f v (x₀ + x)) ≤
        (1 - α) * f v x₀ + α * (⨅ x : Δ, f v (x₀ + x)) + α * devRadius Δ ^ 2 * h := by sorry

end DistInterpRO.Shrinkage
