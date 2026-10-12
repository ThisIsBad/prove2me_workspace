import Mathlib
import Definitions.Def_NagaevLD_LowerBound_Setting

open MeasureTheory ProbabilityTheory

namespace NagaevLD.LowerBound

/-- §1, p. 759: `P(max_{i≠j} X_i ≥ x) ≤ B_n²/x²` (the page prints `> x`; `≥ x` is stronger and is
what the chain needs). -/
theorem chebyshev_max {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : Fin n → Ω → ℝ) (hXm : ∀ i, Measurable (X i))
    (hindep : iIndepFun (fun i => X i) P)
    (hL2 : ∀ i, MemLp (X i) 2 P) (hmean : ∀ i, ∫ ω, X i ω ∂P = 0)
    (x : ℝ) (hx : 0 < x) (j : Fin n) :
    P.real {ω | ∃ i, i ≠ j ∧ x ≤ X i ω} ≤ NagaevLD.FukNagaev.Bn2 P X / x ^ 2 := by sorry

end NagaevLD.LowerBound

