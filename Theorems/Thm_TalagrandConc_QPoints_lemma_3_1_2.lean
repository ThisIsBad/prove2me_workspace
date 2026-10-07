import Mathlib

namespace TalagrandConc.QPoints

open MeasureTheory

/-- Lemma 3.1.2 (3.1.4). -/
theorem lemma_3_1_2 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (q : ℕ) (hq : 2 ≤ q) (g : Ω → ℝ) (hg : Measurable g)
    (hlow : ∀ ω, 1 / (q : ℝ) ≤ g ω) (hup : ∀ ω, g ω ≤ 1) :
    (∫ ω, 1 / g ω ∂μ) * (∫ ω, g ω ∂μ) ^ q ≤ 1 := by sorry

end TalagrandConc.QPoints

