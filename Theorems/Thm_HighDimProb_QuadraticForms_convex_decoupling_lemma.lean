import Mathlib

open MeasureTheory ProbabilityTheory

namespace HighDimProb.QuadraticForms

/-- **Lemma 6.1.2** (the convex decoupling lemma), Vershynin, *High-Dimensional Probability*
(2018), p. 136.

Let `Y` and `Z` be independent random variables such that `E Z = 0`. Then, for every convex
function `F`, one has `E F(Y) ≤ E F(Y + Z)`. -/
theorem convex_decoupling_lemma {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Y Z : Ω → ℝ) (hY : Measurable Y) (hZ : Measurable Z)
    (hindep : IndepFun Y Z P) (hZint : Integrable Z P) (hZmean : ∫ ω, Z ω ∂P = 0)
    (F : ℝ → ℝ) (hF : ConvexOn ℝ Set.univ F)
    (hYF : Integrable (fun ω => F (Y ω)) P)
    (hYZF : Integrable (fun ω => F (Y ω + Z ω)) P) :
    ∫ ω, F (Y ω) ∂P ≤ ∫ ω, F (Y ω + Z ω) ∂P := by sorry

end HighDimProb.QuadraticForms
