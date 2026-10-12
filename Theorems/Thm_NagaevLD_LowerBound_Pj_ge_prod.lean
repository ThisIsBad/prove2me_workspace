import Mathlib
import Definitions.Def_NagaevLD_LowerBound_Setting

open MeasureTheory ProbabilityTheory

namespace NagaevLD.LowerBound

/-- §1, p. 758, after (1.57): `P_j ≥ P(X_j ≥ 2x) P(S_n^j ≥ −x, max_{i≠j} X_i < x)`. -/
theorem Pj_ge_prod {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : Fin n → Ω → ℝ) (hXm : ∀ i, Measurable (X i))
    (hindep : iIndepFun (fun i => X i) P)
    (x : ℝ) (hx : 0 < x) (j : Fin n) :
    P.real {ω | 2 * x ≤ X j ω} *
        P.real {ω | -x ≤ Sj n X j ω ∧ ∀ i, i ≠ j → X i ω < x} ≤ Pj P X x j := by sorry

end NagaevLD.LowerBound

