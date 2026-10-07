import Mathlib

namespace TalagrandConc.QPoints

open MeasureTheory
open scoped ENNReal

/-- Corollary 3.1.3 (3.1.5), with `0 ≤ g_i ≤ 1` (values in `ℝ≥0∞`, `1 / 0 = ⊤`). -/
theorem corollary_3_1_3 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (q : ℕ) (hq : 2 ≤ q) (g : Fin q → Ω → ℝ≥0∞)
    (hg : ∀ i, Measurable (g i)) (hup : ∀ i ω, g i ω ≤ 1) :
    (∫⁻ ω, ⨅ i : Fin q, min (q : ℝ≥0∞) (g i ω)⁻¹ ∂μ) * ∏ i : Fin q, ∫⁻ ω, g i ω ∂μ ≤ 1 := by sorry

end TalagrandConc.QPoints

