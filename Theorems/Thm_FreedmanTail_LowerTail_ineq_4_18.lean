import Mathlib
import Definitions.Def_FreedmanTail_LowerTail_Exponents
import Definitions.Def_FreedmanTail_LowerTail_Hypotheses
import Definitions.Def_FreedmanTail_LowerTail_ProofNotation
open MeasureTheory

namespace FreedmanTail.LowerTail

/-- Freedman (1975), (4.18), p. 110: under (4.11a), for every `x ≥ 0`,
`P{W < x} < exp[−a²/(2(a + x))]`. -/
theorem ineq_4_18 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : Ω → ℝ) (hW : Measurable W) (hW0 : ∀ ω, 0 ≤ W ω) (a : ℝ) (ha : 0 < a)
    (hU : LaplaceUpper P W a) (x : ℝ) (hx : 0 ≤ x) :
    P.real {ω | W ω < x} < Real.exp (-(a ^ 2 / (2 * (a + x)))) := by sorry

end FreedmanTail.LowerTail

