import Mathlib
import Definitions.Def_NagaevLD_LowerBound_Setting

open MeasureTheory ProbabilityTheory

namespace NagaevLD.LowerBound

/-- §1, p. 759: `P(S_n^j ≥ −x) ≥ 1 − B_n²/x²` for centred, square-integrable, independent summands. -/
theorem chebyshev_Sj {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : Fin n → Ω → ℝ) (hXm : ∀ i, Measurable (X i))
    (hindep : iIndepFun (fun i => X i) P)
    (hL2 : ∀ i, MemLp (X i) 2 P) (hmean : ∀ i, ∫ ω, X i ω ∂P = 0)
    (x : ℝ) (hx : 0 < x) (j : Fin n) :
    1 - NagaevLD.FukNagaev.Bn2 P X / x ^ 2 ≤ P.real {ω | -x ≤ Sj n X j ω} := by sorry

end NagaevLD.LowerBound

