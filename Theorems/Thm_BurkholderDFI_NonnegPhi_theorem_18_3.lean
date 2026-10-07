import Mathlib
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace BurkholderDFI.NonnegPhi

/-- Theorem 18.3, p. 36: if `Φ` satisfies the conditions of Section 7 and `f` is a nonnegative
martingale, then `EΦ(S(f)) ≤ cEΦ(f^*)`, where `c` depends only on the growth constant `c_(6.1)`. -/
theorem theorem_18_3 (c : ℝ≥0) :
    ∃ C : ℝ≥0, 0 < C ∧
      ∀ (Ω : Type) [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (ℱ : Filtration ℕ mΩ) (f : ℕ → Ω → ℝ), Martingale f ℱ P → (∀ n, 1 ≤ n → 0 ≤ᵐ[P] f n) →
        ∀ Φ : ℝ≥0∞ → ℝ≥0∞, BurkholderDFI.SquareFnLp.IsPhi Φ c →
          ∫⁻ ω, Φ (BurkholderDFI.SquareFnLp.sqFn f ω) ∂P ≤ (C : ℝ≥0∞) * ∫⁻ ω, Φ (BurkholderDFI.SquareFnLp.maxFn f ω) ∂P := by sorry

end BurkholderDFI.NonnegPhi

