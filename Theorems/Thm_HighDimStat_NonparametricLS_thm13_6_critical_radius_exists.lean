import Mathlib
import Definitions.Def_HighDimStat_NonparametricLS_Core

namespace HighDimStat.NonparametricLS

open MeasureTheory

/-- **Lemma 13.6** (p. 425, PDF 445). For any star-shaped function class `H`, the map
`δ ↦ Gₙ(δ; H)/δ` is non-increasing on `(0, ∞)`. Consequently, for any constant `c > 0`, the
inequality `Gₙ(δ; H)/δ ≤ cδ` has a smallest positive solution. -/
theorem thm13_6_critical_radius_exists {X Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (x : Fin n → X)
    (w : Fin n → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] (hw : IsIIDStdGaussian P w)
    (H : Set (X → ℝ)) (hH : IsStarShaped H) :
    (∀ δ t : ℝ, 0 < δ → δ ≤ t →
        localGaussianComplexity x w P H t / t ≤ localGaussianComplexity x w P H δ / δ) ∧
      ∀ c : ℝ, 0 < c →
        ∃ δ, IsLeast {δ : ℝ | 0 < δ ∧ localGaussianComplexity x w P H δ / δ ≤ c * δ} δ := by sorry

end HighDimStat.NonparametricLS
