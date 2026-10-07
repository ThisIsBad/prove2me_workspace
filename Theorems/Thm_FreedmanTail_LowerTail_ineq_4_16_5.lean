import Mathlib
import Definitions.Def_FreedmanTail_LowerTail_Exponents
import Definitions.Def_FreedmanTail_LowerTail_Hypotheses
import Definitions.Def_FreedmanTail_LowerTail_ProofNotation
open MeasureTheory

namespace FreedmanTail.LowerTail

/-- Freedman (1975), (4.16:5), p. 110: `η₅ < P{W < b} · exp[(−½ + 2δ²)k]`. -/
theorem ineq_4_16_5
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : Ω → ℝ) (hW : Measurable W) (hW0 : ∀ ω, 0 ≤ W ω) (δ a b : ℝ)
    (hU : LaplaceUpper P W a) (hL : LaplaceLower P W a) (hpar : ParamConditions δ a b) :
    eta P W δ a b (I5 δ b) <
      P.real {ω | W ω < b} * Real.exp ((-(1 / 2) + 2 * δ ^ 2) * kStar a b) := by sorry

end FreedmanTail.LowerTail

