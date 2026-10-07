import Mathlib
import Definitions.Def_FreedmanTail_LowerTail_Exponents
import Definitions.Def_FreedmanTail_LowerTail_Hypotheses
import Definitions.Def_FreedmanTail_LowerTail_ProofNotation
open MeasureTheory

namespace FreedmanTail.LowerTail

/-- Freedman (1975), (4.15), p. 109: under (4.11b) and (4.12), with `λ = (1 + δ)a/b`
and `φ(λ) = λ²/2 − λ³/6`,
`φ(λ) ∫_0^∞ P{W < x} exp[−φ(λ)x] dx > exp[−λ(a + 1)]`. -/
theorem ineq_4_15 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : Ω → ℝ) (hW : Measurable W) (hW0 : ∀ ω, 0 ≤ W ω) (δ a b : ℝ)
    (hL : LaplaceLower P W a) (hpar : ParamConditions δ a b) :
    Real.exp (-(lamStar δ a b * (a + 1))) <
      phi (lamStar δ a b) *
        ∫ x in Set.Ici (0 : ℝ), P.real {ω | W ω < x} *
          Real.exp (-(phi (lamStar δ a b) * x)) := by sorry

end FreedmanTail.LowerTail

