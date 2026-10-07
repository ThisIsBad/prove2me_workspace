import Mathlib
import Definitions.Def_FoundationsML_ModelSelection_BayesScore
import Definitions.Def_FoundationsML_ModelSelection_PhiLossPointwise
import Definitions.Def_FoundationsML_ModelSelection_ExpectedPhiLoss
import Definitions.Def_FoundationsML_ModelSelection_ScoringRisk

open MeasureTheory


namespace FoundationsML.ModelSelection

/-- Theorem 4.7 (Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine Learning*, 2nd ed.,
MIT Press 2018, p. 76, PDF p. 93). Let `Φ : ℝ → ℝ` be convex and non-decreasing, `η(x) =
P[y = +1 | x] ∈ [0,1]`, and let `hΦstar` be a pointwise minimizer of the Φ-loss
`u ↦ L_Φ(x, u)` at every `x` (the book's `h*_Φ`, taken real-valued). Assume there exist
`s ≥ 1` and `c > 0` with `|h*(x)|^s ≤ c^s (L_Φ(x,0) − L_Φ(x,h*_Φ(x)))` for all `x`, where
`h*(x) = η(x) − 1/2` is the Bayes scoring function. Then, for any hypothesis `h : X → ℝ`,
`R(h) − R* ≤ 2c (L_Φ(h) − L*_Φ)^{1/s}`.

**Formalization Note.** Replaces `convex_surrogate_bound`, which had no measurability or
integrability hypothesis, so the Bochner integrals defining `L_Φ(h)` could silently be `0`
(disproved with a non-measurable integrand). Now explicit: the book's standing measurability
of `η`, `h` and `h*_Φ` (footnote 2, p. 10), `η` valued in `[0,1]` (it is a conditional
probability), and integrability of the two Φ-loss integrands, i.e. finiteness of `L_Φ(h)` and
`L*_Φ`, which the book's expectations presuppose (if `L_Φ(h) = +∞` the bound is trivially
true and nothing is lost). The classification risks are integrals of `[0,1]`-valued
measurable functions and need no further hypothesis. As in the retired version, the book's
extended-valued choices `h*_Φ(x) = ±∞` at `η(x) ∈ {0,1}` are outside this real-valued
formalization: the theorem applies whenever a real-valued pointwise minimizer is supplied. -/
theorem convex_surrogate_bound_v2 {X : Type*} [MeasurableSpace X] (DX : Measure X)
    [IsProbabilityMeasure DX] (η : X → ℝ) (hη_meas : Measurable η)
    (hη : ∀ x, η x ∈ Set.Icc (0 : ℝ) 1) (Φ : ℝ → ℝ)
    (hΦconv : ConvexOn ℝ Set.univ Φ) (hΦmono : Monotone Φ)
    (hΦstar : X → ℝ) (hΦstar_meas : Measurable hΦstar)
    (hΦstar_min : ∀ x u, PhiLossPointwise η Φ x (hΦstar x) ≤ PhiLossPointwise η Φ x u)
    (hΦstar_int : Integrable (fun x => PhiLossPointwise η Φ x (hΦstar x)) DX)
    (s c : ℝ) (hs : 1 ≤ s) (hc : 0 < c)
    (hbound : ∀ x, |BayesScore η x| ^ s ≤
      c ^ s * (PhiLossPointwise η Φ x 0 - PhiLossPointwise η Φ x (hΦstar x)))
    (h : X → ℝ) (hh_meas : Measurable h)
    (hh_int : Integrable (fun x => PhiLossPointwise η Φ x (h x)) DX) :
    ScoringRisk DX η h - ScoringRisk DX η (BayesScore η) ≤
      2 * c * (ExpectedPhiLoss DX η Φ h - ExpectedPhiLoss DX η Φ hΦstar) ^ (1 / s) := by sorry

end FoundationsML.ModelSelection

