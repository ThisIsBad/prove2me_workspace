import Mathlib
import Definitions.Def_KingmanSubadditive_Continuous_Process

namespace KingmanSubadditive.Continuous

open MeasureTheory Filter Topology

/-- Kingman, §1.4, proof of Theorem 4, (1.4.9), pp. 889–890.
The oscillation on unit intervals, divided by the integer time, tends to
zero almost surely and in mean. `ENNReal` retains any infinite values on a
null set; the nonnegative integral expresses the mean. -/
theorem oscillation_vanishes {S : Type*} [MeasurableSpace S]
    (P : Measure S) [IsProbabilityMeasure P]
    (x : ℝ → ℝ → S → ℝ)
    (hproc : IsProcess P x) (hsep : IsSeparable P x)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a < b)
    (hosc : FiniteOscillation P x (Set.Icc a b)) :
    (∀ᵐ ω ∂P, Tendsto
      (fun n : ℕ => oscillation x (Set.Icc (n : ℝ) ((n : ℝ) + 1)) ω /
        (n : ENNReal)) atTop (𝓝 0)) ∧
    Tendsto (fun n : ℕ =>
      ∫⁻ ω, oscillation x (Set.Icc (n : ℝ) ((n : ℝ) + 1)) ω /
        (n : ENNReal) ∂P) atTop (𝓝 0) := by sorry

end KingmanSubadditive.Continuous

