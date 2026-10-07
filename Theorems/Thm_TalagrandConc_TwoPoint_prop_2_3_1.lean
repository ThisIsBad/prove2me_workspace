import Mathlib
import Definitions.Def_TalagrandConc_TwoPoint_Basic

open MeasureTheory
open scoped ENNReal NNReal

namespace TalagrandConc.TwoPoint

/-- Talagrand (1995), Proposition 2.3.1, Eqs. (2.3.1)–(2.3.3), p. 87. `Ω = {0,1}`,
`P = μ^N` with `μ({1}) = p`, `f` the Hamming distance (2.1.1). For every `A ⊆ Ω^N`,
`t ≥ 0`, `α ≥ 1`: `∫ e^{t f(A,x)} dP(x) ≤ b(α, t, p)^N / P(A)^α`. -/
theorem prop_2_3_1 (p : unitInterval) (N : ℕ) (A : Set (Fin N → Bool))
    (α : ℝ) (hα : 1 ≤ α) (t : ℝ) (ht : 0 ≤ t) :
    (∫⁻ x, TalagrandConc.OnePoint.expMul t (hammingDistToSet A x) ∂(productMeasure N p))
      ≤ ENNReal.ofReal (bConst α t (p : ℝ)) ^ N / (productMeasure N p A) ^ α := by sorry

end TalagrandConc.TwoPoint

