import Mathlib
import Definitions.Def_FreedmanTail_LowerTail_Exponents
import Definitions.Def_FreedmanTail_LowerTail_Hypotheses
open MeasureTheory

namespace FreedmanTail.LowerTail

/-- Freedman (1975), (4.10) Proposition, p. 109. Let `W ≥ 0` be a random variable and `a > 0`
with, for all `λ ≥ 0`, (4.11a) `E{exp[−e(λ)W]} ≤ exp(−λa)` and (4.11b)
`E{exp[−f(λ)W]} ≥ exp(−λ(a + 1))`. Let `δ, a, b > 0` satisfy (4.12a)–(4.12c). Then (4.13)
`P{W < b} > ½ exp[−(½ + 2δ)a²/b]`. -/
theorem proposition_4_10 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : Ω → ℝ) (hW : Measurable W) (hW0 : ∀ ω, 0 ≤ W ω) (δ a b : ℝ)
    (hU : LaplaceUpper P W a) (hL : LaplaceLower P W a) (hpar : ParamConditions δ a b) :
    1 / 2 * Real.exp (-((1 / 2 + 2 * δ) * a ^ 2 / b)) < P.real {ω | W ω < b} := by sorry

end FreedmanTail.LowerTail

