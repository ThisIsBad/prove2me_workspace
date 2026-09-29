import Mathlib
import Definitions.Def_DistInterpRO_Shrinkage_Model

open MeasureTheory
open scoped Pointwise

namespace DistInterpRO.Shrinkage

/-- §4.2, proof of Theorem 4.1 (p. 105), third display: under the Hessian bound
`−hI ⪯ H_v ⪯ hI`, the gradient `g_v` is `h`-Lipschitz, and in particular
`‖g_v(x₀ + βx₁) − g_v(x₀ + αβ′x₁)‖ ≤ h‖βx₁ − αβ′x₁‖ ≤ h‖x₁‖ ≤ hD`
for `β, β′ ∈ [0, 1]`, `α ∈ (0, 1)`, `x₁ ∈ Δ`, `D = max_{x ∈ Δ} ‖x‖₂`. -/
theorem gradient_bound {m : ℕ} {V : Type*} (f : V → EuclideanSpace ℝ (Fin m) → ℝ) (v : V)
    (h : ℝ) (hh : 0 ≤ h) (hf : HasBoundedHessian (f v) h) :
    (∀ a b : EuclideanSpace ℝ (Fin m),
        ‖fderiv ℝ (f v) a - fderiv ℝ (f v) b‖ ≤ h * ‖a - b‖) ∧
    ∀ (Δ : Set (EuclideanSpace ℝ (Fin m))), IsCompact Δ →
      ∀ (α : ℝ), 0 < α → α < 1 →
      ∀ (x₀ x₁ : EuclideanSpace ℝ (Fin m)), x₁ ∈ Δ →
      ∀ β ∈ Set.Icc (0 : ℝ) 1, ∀ β' ∈ Set.Icc (0 : ℝ) 1,
        ‖fderiv ℝ (f v) (x₀ + β • x₁) - fderiv ℝ (f v) (x₀ + (α * β') • x₁)‖ ≤
            h * ‖β • x₁ - (α * β') • x₁‖ ∧
          h * ‖β • x₁ - (α * β') • x₁‖ ≤ h * ‖x₁‖ ∧
          h * ‖x₁‖ ≤ h * devRadius Δ := by sorry

end DistInterpRO.Shrinkage
