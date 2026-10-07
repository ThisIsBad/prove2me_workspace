import Mathlib
import Definitions.Def_TalagrandConc_QPoints_Basic

namespace TalagrandConc.QPoints

open MeasureTheory
open scoped ENNReal

/-- Theorem 3.1.1: (3.1.2) and (3.1.3). -/
theorem theorem_3_1_1 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (N q : ℕ) (hq : 2 ≤ q) :
    (∀ A : Fin q → Set (Fin N → Ω), (∀ i, MeasurableSet (A i)) →
        Measurable (qDist A) →
        ∫⁻ x, epow (q : ℝ≥0∞) (qDist A x) ∂(Measure.pi fun _ : Fin N => μ) ≤
          (∏ i : Fin q, (Measure.pi fun _ : Fin N => μ) (A i))⁻¹) ∧
    (∀ (A : Set (Fin N → Ω)) (k : ℕ), MeasurableSet A →
        Measurable (qDist (fun _ : Fin q => A)) →
        (Measure.pi fun _ : Fin N => μ) {x | (k : ℕ∞) ≤ qDist (fun _ : Fin q => A) x} ≤
          ((q : ℝ≥0∞) ^ k * (Measure.pi fun _ : Fin N => μ) A ^ q)⁻¹) := by sorry

end TalagrandConc.QPoints

