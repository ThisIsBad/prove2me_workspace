import Mathlib
import Definitions.Def_StoneRegression_Criterion_Setting
import Definitions.Def_StoneRegression_Quantile_Quantiles

namespace StoneRegression.Quantile

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

/-- Proposition 14, p. 616 (range of `r` corrected from the printed `r > 1` to `r ≥ 1`, the range the
proof of Theorem 3 uses): `E|L(p|X)|ʳ ≤ E|Y|ʳ / (p ∧ (1 − p))` and the same for `U(p|X)`, with all
expectations as `ℝ≥0∞`-valued lower integrals (both sides may be `∞`). -/
theorem proposition_14 {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (κ : Kernel (EuclideanSpace ℝ (Fin d)) ℝ) [IsMarkovKernel κ]
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (r : ℝ) (hr : 1 ≤ r) :
    ∫⁻ x, ‖lowerQ κ p x‖ₑ ^ r ∂μ ≤
        (∫⁻ q, ‖q.2‖ₑ ^ r ∂(μ ⊗ₘ κ)) / ENNReal.ofReal (min p (1 - p)) ∧
    ∫⁻ x, ‖upperQ κ p x‖ₑ ^ r ∂μ ≤
        (∫⁻ q, ‖q.2‖ₑ ^ r ∂(μ ⊗ₘ κ)) / ENNReal.ofReal (min p (1 - p)) := by sorry

end StoneRegression.Quantile

