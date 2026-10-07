import Mathlib
import Definitions.Def_FreedmanTail_Bernstein_Exponents

open MeasureTheory ProbabilityTheory

namespace FreedmanTail.Bernstein

/-- Freedman (1975), display (3.5), p. 106: for `λ ≥ 0` and a random variable `X` with
`X ≤ 1` and `E X ≤ 0`, `E exp(λX) ≤ 1 + e(λ) Var X ≤ exp[e(λ) Var X]`.
`X` is square integrable (the page reduces to that case: "It is enough to prove (3.5)
when E(X²) < ∞"). -/
theorem ineq_3_5 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (lam : ℝ) (hlam : 0 ≤ lam)
    (hX2 : MemLp X 2 P) (hX1 : X ≤ᵐ[P] 1) (hmean : ∫ ω, X ω ∂P ≤ 0) :
    ∫ ω, Real.exp (lam * X ω) ∂P ≤ 1 + e lam * variance X P ∧
      1 + e lam * variance X P ≤ Real.exp (e lam * variance X P) := by sorry

end FreedmanTail.Bernstein

