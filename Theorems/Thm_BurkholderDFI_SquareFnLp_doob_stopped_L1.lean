import Mathlib
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale

namespace BurkholderDFI.SquareFnLp

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

theorem doob_stopped_L1 {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ℱ : Filtration ℕ mΩ} {f : ℕ → Ω → ℝ}
    (hf : Martingale f ℱ P ∨ (Submartingale f ℱ P ∧ ∀ n, 1 ≤ n → 0 ≤ᵐ[P] f n))
    (hL1 : pNorm P 1 f < ⊤) (μ : Ω → ℕ∞) (hμ : IsStoppingTime ℱ μ) :
    ∃ fInf : Ω → ℝ, (∀ᵐ ω ∂P, Tendsto (fun n => f n ω) atTop (𝓝 (fInf ω))) ∧
      ∫⁻ ω, ENNReal.ofReal |valAt f fInf (μ ω) ω| ∂P ≤ pNorm P 1 f := by sorry

end BurkholderDFI.SquareFnLp

