import Mathlib
import Definitions.Def_NagaevLD_LowerBound_Setting

open MeasureTheory ProbabilityTheory

namespace NagaevLD.LowerBound

/-- (1.58), p. 759: `P_j ≥ ½ P(X_j ≥ 2x)` if `x ≥ 2B_n`. -/
theorem eq_1_58 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : Fin n → Ω → ℝ) (hXm : ∀ i, Measurable (X i))
    (hindep : iIndepFun (fun i => X i) P)
    (hL2 : ∀ i, MemLp (X i) 2 P) (hmean : ∀ i, ∫ ω, X i ω ∂P = 0)
    (x : ℝ) (hx : 0 < x) (hxB : 2 * Real.sqrt (NagaevLD.FukNagaev.Bn2 P X) ≤ x) (j : Fin n) :
    (1 / 2) * P.real {ω | 2 * x ≤ X j ω} ≤ Pj P X x j := by sorry

end NagaevLD.LowerBound

