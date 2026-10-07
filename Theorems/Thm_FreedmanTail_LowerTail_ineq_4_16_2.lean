import Mathlib
import Definitions.Def_FreedmanTail_LowerTail_Exponents
import Definitions.Def_FreedmanTail_LowerTail_Hypotheses
import Definitions.Def_FreedmanTail_LowerTail_ProofNotation
open MeasureTheory

namespace FreedmanTail.LowerTail

/-- Freedman (1975), (4.16:i) for `i = 2`, p. 110: `η₂ < (1/8) exp[−(1 + δ)k]`. -/
theorem ineq_4_16_2
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : Ω → ℝ) (hW : Measurable W) (hW0 : ∀ ω, 0 ≤ W ω) (δ a b : ℝ)
    (hU : LaplaceUpper P W a) (hL : LaplaceLower P W a) (hpar : ParamConditions δ a b) :
    eta P W δ a b (I2 δ a b) < 1 / 8 * Real.exp (-((1 + δ) * kStar a b)) := by sorry

end FreedmanTail.LowerTail

