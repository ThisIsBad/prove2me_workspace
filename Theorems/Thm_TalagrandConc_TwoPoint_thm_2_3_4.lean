import Mathlib
import Definitions.Def_TalagrandConc_TwoPoint_Basic

open MeasureTheory
open scoped ENNReal NNReal

namespace TalagrandConc.TwoPoint

/-- Talagrand (1995), Theorem 2.3.4, Eq. (2.3.6), p. 90. `Ω = {0,1}`, `P = μ^N` with
`μ({1}) = p`, and `P₁ = μ₁^N` with `μ₁({1}) = p₁ > p`. For every `A ⊆ Ω^N`, `α > 0`
(the range of §2.2; the page does not restate it) and `t ≥ 0`,
`∫ e^{t f(A,x)} dP(x) ≤ a(α, t)^N / P₁(A)^α` for the one-sided distance `f`. -/
theorem thm_2_3_4 (p p₁ : unitInterval) (hpp₁ : p < p₁)
    (N : ℕ) (A : Set (Fin N → Bool)) (α : ℝ) (hα : 0 < α) (t : ℝ) (ht : 0 ≤ t) :
    (∫⁻ x, TalagrandConc.OnePoint.expMul t (oneSidedDistToSet A x) ∂(productMeasure N p))
      ≤ ENNReal.ofReal (aConst α t (p : ℝ) (p₁ : ℝ)) ^ N / (productMeasure N p₁ A) ^ α := by sorry

end TalagrandConc.TwoPoint

