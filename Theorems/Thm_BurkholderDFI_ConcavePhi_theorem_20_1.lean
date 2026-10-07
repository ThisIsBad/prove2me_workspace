import Mathlib
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace BurkholderDFI.ConcavePhi

/-- Theorem 20.1, p. 38: for `Φ` concave and satisfying the conditions of Section 7, and
nonnegative measurable `z_1, z_2, …`,
`EΦ(Σ_{k=1}^∞ z_k) ≤ 2EΦ(Σ_{k=1}^∞ E(z_k|𝒜_{k−1}))` (20.1). Here `z (k+1)` is `z_{k+1}` and
`condLExp (ℱ k) P (z (k+1))` is `E(z_{k+1}|𝒜_k)`. -/
theorem theorem_20_1 {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (ℱ : Filtration ℕ mΩ) (Φ : ℝ≥0∞ → ℝ≥0∞) (c : ℝ≥0)
    (hΦ : BurkholderDFI.SquareFnLp.IsPhi Φ c) (hcc : BurkholderDFI.SquareFnLp.IsConcavePhi Φ) (z : ℕ → Ω → ℝ≥0∞) (hz : ∀ k, Measurable (z k)) :
    ∫⁻ ω, Φ (∑' k, z (k + 1) ω) ∂P
      ≤ 2 * ∫⁻ ω, Φ (∑' k, condLExp (ℱ k) P (z (k + 1)) ω) ∂P := by sorry

end BurkholderDFI.ConcavePhi

