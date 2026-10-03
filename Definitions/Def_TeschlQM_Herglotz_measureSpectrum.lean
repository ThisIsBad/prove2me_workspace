import Mathlib

open MeasureTheory

namespace TeschlQM.Herglotz

/-- Teschl, p. 99, (3.59): the **spectrum** of a Borel measure `μ` on `ℝ`, the set of its growth
points, `σ(μ) = {λ ∈ ℝ | μ((λ − ε, λ + ε)) > 0 for all ε > 0}`. -/
def measureSpectrum (μ : Measure ℝ) : Set ℝ :=
  {t : ℝ | ∀ ε : ℝ, 0 < ε → 0 < μ (Set.Ioo (t - ε) (t + ε))}

end TeschlQM.Herglotz
