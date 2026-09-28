import Mathlib
import Definitions.Def_DistInterpRO_Shrinkage_Model

open MeasureTheory
open scoped Pointwise

namespace DistInterpRO.Shrinkage

/-- §4.2, proof of Theorem 4.1 (p. 105), first display: the mean-value step
`f(v, x₀ + x₁) = f(v, x₀) + g_v(x₀ + βx₁)x₁` for some `β ∈ [0, 1]`, where
`g_v(y)z = fderiv ℝ (f v) y z`. -/
theorem mean_value_step {m : ℕ} {V : Type*} (f : V → EuclideanSpace ℝ (Fin m) → ℝ) (v : V)
    (hf : Differentiable ℝ (f v)) (x₀ x₁ : EuclideanSpace ℝ (Fin m)) :
    ∃ β ∈ Set.Icc (0 : ℝ) 1, f v (x₀ + x₁) = f v x₀ + fderiv ℝ (f v) (x₀ + β • x₁) x₁ := by sorry

end DistInterpRO.Shrinkage
