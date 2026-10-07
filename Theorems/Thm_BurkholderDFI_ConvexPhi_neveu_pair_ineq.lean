import Mathlib
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale

namespace BurkholderDFI.ConvexPhi
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- §16, p. 34: Neveu's cited pair inequality. -/
theorem neveu_pair_ineq {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℕ mΩ)
    (z : ℕ → Ω → ℝ≥0∞) (hz : ∀ k, Measurable (z k)) :
    ∀ l : ℝ, 0 < l →
      (∫⁻ ω in {ω | ENNReal.ofReal l <
        ∑' k : ℕ, condLExp (ℱ k) P (z (k + 1)) ω},
        ((∑' k : ℕ, condLExp (ℱ k) P (z (k + 1)) ω) - ENNReal.ofReal l) ∂P)
      ≤ (∫⁻ ω in {ω | ENNReal.ofReal l <
        ∑' k : ℕ, condLExp (ℱ k) P (z (k + 1)) ω},
        (∑' k : ℕ, z (k + 1) ω) ∂P) := by sorry
end BurkholderDFI.ConvexPhi

