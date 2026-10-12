import Mathlib
import Definitions.Def_NagaevLD_GenMoment_Setting

open MeasureTheory ProbabilityTheory

namespace NagaevLD.GenMoment

/-- (2.45), p. 767: the exponential Chebyshev (Chernoff) bound for the sum of independent
summands, `P(S_n ≥ x) ≤ e^{-hx} ∏ E e^{h X_j}` for `h ≥ 0`. -/
theorem eq_2_45 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (hn : 0 < n) (X : Fin n → Ω → ℝ) (hXm : ∀ j, Measurable (X j)) (hind : iIndepFun X P)
    (x : ℝ) (hx : 0 < x) (h : ℝ) (hh : 0 ≤ h)
    (hint : ∀ j, Integrable (fun ω => Real.exp (h * X j ω)) P) :
    P.real {ω | x ≤ NagaevLD.FukNagaev.S n X ω} ≤ Real.exp (-(h * x)) * ∏ j, ∫ ω, Real.exp (h * X j ω) ∂P := by sorry

end NagaevLD.GenMoment

