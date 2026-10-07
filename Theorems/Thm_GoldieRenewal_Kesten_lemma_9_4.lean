import Mathlib

namespace GoldieRenewal.Kesten

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- **Lemma 9.4** (Goldie, *Implicit renewal theory and tails of solutions of random equations*,
Ann. Appl. Probab. 1(1) (1991), p. 149). Let `κ > 0` and let `X`, `Y` be random variables on a
common probability space.

* (9.17), corrected to an inequality:
  `∫₀^∞ |P(X > t) − P(Y > t)| t^{κ−1} dt ≤ κ⁻¹ E|(X⁺)^κ − (Y⁺)^κ|`, finite or infinite.
* (9.18): when `E|(X⁺)^κ − (Y⁺)^κ| < ∞`, the function `t ↦ (P(X > t) − P(Y > t)) t^{κ−1}` is
  integrable on `(0, ∞)` and `∫₀^∞ (P(X > t) − P(Y > t)) t^{κ−1} dt = κ⁻¹ E((X⁺)^κ − (Y⁺)^κ)`.

**Formalization Note** (9.17) is printed as an equality; only `≤` holds (for `X`, `Y` i.i.d. and
non-degenerate the left side is `0` and the right side positive), and the paper's proof and its
use in Corollary 2.4 need only `≤`. Both sides of (9.17) are lower Lebesgue integrals in `[0, ∞]`,
so "finite or infinite" is literal. `x⁺ = max x 0`. -/
theorem lemma_9_4 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0 < κ) (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y) :
    (∫⁻ t in Set.Ioi (0 : ℝ),
        ENNReal.ofReal (|P.real {ω | t < X ω} - P.real {ω | t < Y ω}| * t ^ (κ - 1))
      ≤ ENNReal.ofReal κ⁻¹ *
        ∫⁻ ω, ENNReal.ofReal |(max (X ω) 0) ^ κ - (max (Y ω) 0) ^ κ| ∂P) ∧
    (Integrable (fun ω => (max (X ω) 0) ^ κ - (max (Y ω) 0) ^ κ) P →
      IntegrableOn (fun t : ℝ => (P.real {ω | t < X ω} - P.real {ω | t < Y ω}) * t ^ (κ - 1))
          (Set.Ioi 0) ∧
        ∫ t in Set.Ioi (0 : ℝ), (P.real {ω | t < X ω} - P.real {ω | t < Y ω}) * t ^ (κ - 1)
          = κ⁻¹ * ∫ ω, ((max (X ω) 0) ^ κ - (max (Y ω) 0) ^ κ) ∂P) := by sorry

end GoldieRenewal.Kesten

