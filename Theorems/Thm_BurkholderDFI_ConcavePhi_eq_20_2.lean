import Mathlib
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace BurkholderDFI.ConcavePhi

/-- (20.2), proof of Theorem 20.1, p. 38: `E(Z ∧ λ) ≤ 2E(W ∧ λ)`, `λ > 0`, where
`Z = Σ_{k=1}^∞ z_k` and `W = Σ_{k=1}^∞ E(z_k|𝒜_{k−1})`. Here `z (k+1)` is `z_{k+1}` and
`condLExp (ℱ k) P (z (k+1))` is `E(z_{k+1}|𝒜_k)`. -/
theorem eq_20_2 {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (ℱ : Filtration ℕ mΩ) (z : ℕ → Ω → ℝ≥0∞) (hz : ∀ k, Measurable (z k))
    (l : ℝ≥0) (hl : 0 < l) :
    ∫⁻ ω, min (∑' k, z (k + 1) ω) (l : ℝ≥0∞) ∂P
      ≤ 2 * ∫⁻ ω, min (∑' k, condLExp (ℱ k) P (z (k + 1)) ω) (l : ℝ≥0∞) ∂P := by sorry

end BurkholderDFI.ConcavePhi

