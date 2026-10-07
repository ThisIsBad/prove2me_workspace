import Mathlib
import Definitions.Def_FreedmanTail_Laplace_Exponents

open MeasureTheory ProbabilityTheory

namespace FreedmanTail.Laplace

/-- Freedman (1975), (3.7), p. 107: `E{exp(λX)} ≥ exp{f(λ) Var X}` for random variables `X`
with `X ≥ −1` and `E(X) = 0`, for every `λ ≥ 0`. The expectation of `exp(λX)` (which need not
be integrable, `X` being bounded only below) is a lower Lebesgue integral in `[0, ∞]`; `X` is
assumed square-integrable so that `Var X` is finite. -/
theorem ineq_3_7 {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → ℝ) (hX_L2 : MemLp X 2 P)
    (hX_ge : ∀ᵐ ω ∂P, -1 ≤ X ω) (hX_mean : P[X] = 0)
    (lam : ℝ) (hlam : 0 ≤ lam) :
    ENNReal.ofReal (Real.exp (f lam * variance X P)) ≤
      ∫⁻ ω, ENNReal.ofReal (Real.exp (lam * X ω)) ∂P := by sorry

end FreedmanTail.Laplace

