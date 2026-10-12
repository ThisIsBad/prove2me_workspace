import Mathlib
import Definitions.Def_NagaevLD_LowerBound_Setting

open MeasureTheory ProbabilityTheory

namespace NagaevLD.LowerBound

/-- (1.57), p. 758: `P(S_n ≥ x) ≥ Σ_j P(S_n ≥ x, X_j ≥ x, max_{i≠j} X_i < x) = Σ_j P_j`. -/
theorem eq_1_57 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : Fin n → Ω → ℝ) (hXm : ∀ i, Measurable (X i)) (x : ℝ) :
    ∑ j, Pj P X x j ≤ P.real {ω | x ≤ NagaevLD.FukNagaev.S n X ω} := by sorry

end NagaevLD.LowerBound

