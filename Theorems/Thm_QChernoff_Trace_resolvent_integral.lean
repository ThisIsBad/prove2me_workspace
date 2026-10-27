import Mathlib

namespace QChernoff.Trace

/-- Proof of Lemma 1, Appendix A, p. 4: for `x > 0` and `Δ = A − B`, the resolvent difference
`A(A + x)⁻¹ − B(B + x)⁻¹` equals `∫₀¹ d/dt (B + tΔ)(B + tΔ + x)⁻¹ dt`, which in turn equals
`∫₀¹ x (B + tΔ + x)⁻¹ Δ (B + tΔ + x)⁻¹ dt`; both integrands are integrable on `[0, 1]`. -/
theorem resolvent_integral {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (A B : H →L[ℂ] H) (hA : 0 ≤ A) (hB : 0 ≤ B) (x : ℝ) (hx : 0 < x) :
    IntervalIntegrable
        (deriv (fun τ : ℝ => (B + τ • (A - B)) * Ring.inverse (B + τ • (A - B) + (x : ℂ) • 1)))
        MeasureTheory.volume 0 1 ∧
      IntervalIntegrable
        (fun t : ℝ => x • (Ring.inverse (B + t • (A - B) + (x : ℂ) • 1) * (A - B) *
          Ring.inverse (B + t • (A - B) + (x : ℂ) • 1)))
        MeasureTheory.volume 0 1 ∧
      A * Ring.inverse (A + (x : ℂ) • 1) - B * Ring.inverse (B + (x : ℂ) • 1) =
        ∫ t in (0 : ℝ)..1,
          deriv (fun τ : ℝ => (B + τ • (A - B)) * Ring.inverse (B + τ • (A - B) + (x : ℂ) • 1)) t ∧
      ∫ t in (0 : ℝ)..1,
          deriv (fun τ : ℝ => (B + τ • (A - B)) * Ring.inverse (B + τ • (A - B) + (x : ℂ) • 1)) t =
        ∫ t in (0 : ℝ)..1, x • (Ring.inverse (B + t • (A - B) + (x : ℂ) • 1) * (A - B) *
          Ring.inverse (B + t • (A - B) + (x : ℂ) • 1)) := by sorry

end QChernoff.Trace

