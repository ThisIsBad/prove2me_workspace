import Mathlib
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace BurkholderDFI.CondSquare

/-- Theorem 21.1, p. 39: for every `Φ` satisfying the conditions of Section 7 and every martingale
`f`, `EΦ(f^*) ≤ cEΦ(s(f)) + cEΦ(d^*)`, where `c` depends only on the growth constant `c_(6.1)`. -/
theorem theorem_21_1 (c : ℝ≥0) :
    ∃ C : ℝ≥0, 0 < C ∧
      ∀ (Ω : Type) [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (ℱ : Filtration ℕ mΩ) (f : ℕ → Ω → ℝ), Martingale f ℱ P →
        ∀ Φ : ℝ≥0∞ → ℝ≥0∞, BurkholderDFI.SquareFnLp.IsPhi Φ c →
          ∫⁻ ω, Φ (BurkholderDFI.SquareFnLp.maxFn f ω) ∂P
            ≤ (C : ℝ≥0∞) * ∫⁻ ω, Φ (BurkholderDFI.SquareFnLp.condSqFn ℱ P f ω) ∂P
              + (C : ℝ≥0∞) * ∫⁻ ω, Φ (BurkholderDFI.SquareFnLp.maxFn (BurkholderDFI.SquareFnLp.dseq f) ω) ∂P := by sorry

end BurkholderDFI.CondSquare

