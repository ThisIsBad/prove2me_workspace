import Mathlib
import Definitions.Def_NagaevLD_LowerBound_Setting

open MeasureTheory ProbabilityTheory

namespace NagaevLD.LowerBound

/-- §1, p. 759, "It is clear that": `P(S_n^j ≥ −x, max_{i≠j} X_i < x) ≥ P(S_n^j ≥ −x) − P(max_{i≠j} X_i ≥ x)`
(the page prints `≤ x` and `> x`; this is the form the chain uses with (1.57)'s `< x`). -/
theorem clear_step {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : Fin n → Ω → ℝ) (hXm : ∀ i, Measurable (X i)) (x : ℝ) (j : Fin n) :
    P.real {ω | -x ≤ Sj n X j ω} - P.real {ω | ∃ i, i ≠ j ∧ x ≤ X i ω} ≤
      P.real {ω | -x ≤ Sj n X j ω ∧ ∀ i, i ≠ j → X i ω < x} := by sorry

end NagaevLD.LowerBound

