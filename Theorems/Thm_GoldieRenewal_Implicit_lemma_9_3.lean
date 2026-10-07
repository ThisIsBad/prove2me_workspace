import Mathlib
open MeasureTheory Filter Topology

namespace GoldieRenewal.Implicit

/-- **Lemma 9.3** (Goldie 1991, Ann. Appl. Probab. 1(1), p. 143). If
`∫₀^t u^κ P(R > u) du ~ C₊ t` as `t → ∞`, then `P(R > t) ~ C₊ t^{−κ}` as `t → ∞`.

**Formalization Note** `R` is any real random variable and `κ > 0` (the standing exponent of §2).
"`~ C₊ t`" is read as `(∫₀^t u^κ P(R > u) du) / t → C₊` and "`P(R > t) ~ C₊ t^{−κ}`" as
`t^κ P(R > t) → C₊`, which includes the case `C₊ = 0` read as `o(t)` and `o(t^{−κ})` (the paper's
convention, p. 130). The integrand is bounded and measurable on `[0, t]`, so the interval integral is
the paper's value. -/
theorem lemma_9_3 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (R : Ω → ℝ) (hR : Measurable R) (κ : ℝ) (hκ : 0 < κ) (C : ℝ)
    (h : Tendsto (fun t : ℝ => (∫ u in (0 : ℝ)..t, u ^ κ * P.real {ω | u < R ω}) / t)
      atTop (𝓝 C)) :
    Tendsto (fun t : ℝ => t ^ κ * P.real {ω | t < R ω}) atTop (𝓝 C) := by sorry

end GoldieRenewal.Implicit

