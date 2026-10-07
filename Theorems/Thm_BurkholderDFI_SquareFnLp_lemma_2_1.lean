import Mathlib
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale

namespace BurkholderDFI.SquareFnLp

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

theorem lemma_2_1 {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℕ mΩ} {f : ℕ → Ω → ℝ}
    (hf : Martingale f ℱ P ∨ (Submartingale f ℱ P ∧ ∀ n, 1 ≤ n → 0 ≤ᵐ[P] f n))
    (hL1 : pNorm P 1 f < ⊤) (fInf : Ω → ℝ)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n => f n ω) atTop (𝓝 (fInf ω)))
    (l : ℝ) (hl : 0 < l) :
    (∫⁻ ω, sqFnAt f (exitTime f l ω - 1) ω ^ 2 ∂P
        + ∫⁻ ω, ENNReal.ofReal (valAt f fInf (exitTime f l ω - 1) ω ^ 2) ∂P
      ≤ ENNReal.ofReal (2 * ∫ ω, valAt f fInf (exitTime f l ω) ω
                                 * valAt f fInf (exitTime f l ω - 1) ω ∂P)) ∧
    (2 * ∫ ω, valAt f fInf (exitTime f l ω) ω * valAt f fInf (exitTime f l ω - 1) ω ∂P
      ≤ 2 * l * (pNorm P 1 f).toReal) ∧
    (Martingale f ℱ P →
      ∫⁻ ω, sqFnAt f (exitTime f l ω - 1) ω ^ 2 ∂P
          + ∫⁻ ω, ENNReal.ofReal (valAt f fInf (exitTime f l ω - 1) ω ^ 2) ∂P
        = ENNReal.ofReal (2 * ∫ ω, valAt f fInf (exitTime f l ω) ω
                                   * valAt f fInf (exitTime f l ω - 1) ω ∂P)) := by sorry

end BurkholderDFI.SquareFnLp

