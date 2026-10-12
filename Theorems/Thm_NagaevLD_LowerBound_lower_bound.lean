import Mathlib
import Definitions.Def_NagaevLD_LowerBound_Setting

open MeasureTheory ProbabilityTheory

namespace NagaevLD.LowerBound

/-- §1, p. 759, after (1.58): for `EX_i = 0`, `B_n² < ∞` and `x ≥ 2B_n`,
`P(S_n ≥ x) ≥ ½ Σ_j P(X_j ≥ 2x)`. -/
theorem lower_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : Fin n → Ω → ℝ) (hXm : ∀ i, Measurable (X i))
    (hindep : iIndepFun (fun i => X i) P)
    (hL2 : ∀ i, MemLp (X i) 2 P) (hmean : ∀ i, ∫ ω, X i ω ∂P = 0)
    (x : ℝ) (hx : 0 < x) (hxB : 2 * Real.sqrt (NagaevLD.FukNagaev.Bn2 P X) ≤ x) :
    (1 / 2) * ∑ j, P.real {ω | 2 * x ≤ X j ω} ≤ P.real {ω | x ≤ NagaevLD.FukNagaev.S n X ω} := by sorry

end NagaevLD.LowerBound

