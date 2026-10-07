import Mathlib
import Definitions.Def_FreedmanTail_LowerTail_Exponents
open MeasureTheory

namespace FreedmanTail.LowerTail

/-- Freedman (1975), (4.11a), p. 109: for every `λ ≥ 0`,
`E{exp[−e(λ)W]} ≤ exp(−λa)`. For `λ ≥ 0` and `W ≥ 0` the integrand lies in `(0, 1]`,
so the Bochner integral is a genuine expectation. -/
def LaplaceUpper {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (W : Ω → ℝ) (a : ℝ) : Prop :=
  ∀ lam : ℝ, 0 ≤ lam → ∫ ω, Real.exp (-(e lam * W ω)) ∂P ≤ Real.exp (-(lam * a))

/-- Freedman (1975), (4.11b), p. 109: for every `λ ≥ 0`,
`E{exp[−f(λ)W]} ≥ exp(−λ(a + 1))`. -/
def LaplaceLower {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (W : Ω → ℝ) (a : ℝ) : Prop :=
  ∀ lam : ℝ, 0 ≤ lam → Real.exp (-(lam * (a + 1))) ≤ ∫ ω, Real.exp (-(f lam * W ω)) ∂P

/-- Freedman (1975), (4.12a)–(4.12c), p. 109: `δ, a, b` positive with
`δ < 1/3`, `b/a > 9/δ²` and `a²/b > (16/δ²) log(64/δ²)`. -/
def ParamConditions (δ a b : ℝ) : Prop :=
  0 < δ ∧ 0 < a ∧ 0 < b ∧ δ < 1 / 3 ∧ 9 / δ ^ 2 < b / a ∧
    16 / δ ^ 2 * Real.log (64 / δ ^ 2) < a ^ 2 / b

end FreedmanTail.LowerTail
