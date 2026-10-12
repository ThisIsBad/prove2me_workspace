import Mathlib
import Definitions.Def_NagaevLD_GenMoment_Setting

open MeasureTheory ProbabilityTheory

namespace NagaevLD.GenMoment

/-- (2.46), p. 767: splitting `E e^{h X_j}` at `0` and bounding the part on `X_j ≥ 0` by
`b_gj` times any upper bound `M` of `e^{hu - g(u)}` over `u ≥ 0` (the supremum of the page).
The nonnegative tilt is the one used in the proof of Theorem 2.5. -/
theorem eq_2_46 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : Fin n → Ω → ℝ) (hXm : ∀ j, Measurable (X j)) (g : ℝ → ℝ) (j : Fin n)
    (hbg : IntegrableOn (fun ω => Real.exp (g (X j ω))) {ω | 0 ≤ X j ω} P)
    (h M : ℝ) (hh : 0 ≤ h) (hM : ∀ u : ℝ, 0 ≤ u → Real.exp (h * u - g u) ≤ M) :
    (∫ ω, Real.exp (h * X j ω) ∂P) =
        (∫ ω in {ω | X j ω < 0}, Real.exp (h * X j ω) ∂P) +
          (∫ ω in {ω | 0 ≤ X j ω},
            Real.exp (h * X j ω - g (X j ω)) * Real.exp (g (X j ω)) ∂P) ∧
      (∫ ω, Real.exp (h * X j ω) ∂P)
        ≤ (∫ ω in {ω | X j ω < 0}, Real.exp (h * X j ω) ∂P) + bg P X g j * M := by sorry

end NagaevLD.GenMoment

