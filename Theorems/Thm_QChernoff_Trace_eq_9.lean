import Mathlib

namespace QChernoff.Trace

/-- Eq. (9), p. 4, in the operator form used in Appendix A (corrected: `0 < t < 1`): the
integrand is Bochner integrable on `(0, ∞)` and `A ^ t = (sin(tπ)/π) ∫₀^∞ x^{t−1} A (A + x)⁻¹ dx`. -/
theorem eq_9 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →L[ℂ] H) (hA : 0 ≤ A) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    MeasureTheory.IntegrableOn
        (fun x : ℝ => x ^ (t - 1) • (A * Ring.inverse (A + (x : ℂ) • 1))) (Set.Ioi 0) ∧
      A ^ t = (Real.sin (t * Real.pi) / Real.pi) •
        ∫ x in Set.Ioi (0 : ℝ), x ^ (t - 1) • (A * Ring.inverse (A + (x : ℂ) • 1)) := by sorry

end QChernoff.Trace

