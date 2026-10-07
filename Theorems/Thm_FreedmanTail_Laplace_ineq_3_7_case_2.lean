import Mathlib
import Definitions.Def_FreedmanTail_Laplace_Exponents

open MeasureTheory ProbabilityTheory

namespace FreedmanTail.Laplace

/-- Freedman (1975), proof of (3.7), Case 2, p. 107: if `X` takes only the two values `−b`
and `a`, with `a > 0` and `0 < b ≤ 1`, and has mean `0`, then
`E{exp(λX)} ≥ exp{f(λ) Var X}` for every `λ ≥ 0`. -/
theorem ineq_3_7_case_2 {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → ℝ) (hX_meas : AEMeasurable X P)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hb1 : b ≤ 1)
    (hX_two : ∀ᵐ ω ∂P, X ω = -b ∨ X ω = a) (hX_mean : P[X] = 0)
    (lam : ℝ) (hlam : 0 ≤ lam) :
    Real.exp (f lam * variance X P) ≤ ∫ ω, Real.exp (lam * X ω) ∂P := by sorry

end FreedmanTail.Laplace

