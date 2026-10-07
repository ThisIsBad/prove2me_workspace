import Mathlib
import Definitions.Def_FreedmanTail_LowerTail_Exponents
import Definitions.Def_FreedmanTail_LowerTail_Hypotheses
import Definitions.Def_FreedmanTail_LowerTail_ProofNotation
open MeasureTheory

namespace FreedmanTail.LowerTail

/-- Freedman (1975), (4.19), p. 110, corrected: under (4.11), (4.12), if `0 ≤ x ≤ Na` then
`P{W < x} < θ = (1/8 − 1/50) exp[−(1 + δ)k]`. The page prints `exp[−(1 + δ)]`, without the
factor `k = a²/b`; the proof on the page, and its use in (4.16:1), give the form with `k`. -/
theorem ineq_4_19
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : Ω → ℝ) (hW : Measurable W) (hW0 : ∀ ω, 0 ≤ W ω) (δ a b : ℝ)
    (hU : LaplaceUpper P W a) (hL : LaplaceLower P W a) (hpar : ParamConditions δ a b) :
    ∀ x : ℝ, 0 ≤ x → x ≤ NStar δ * a →
      P.real {ω | W ω < x} < (1 / 8 - 1 / 50) * Real.exp (-((1 + δ) * kStar a b)) := by sorry

end FreedmanTail.LowerTail

