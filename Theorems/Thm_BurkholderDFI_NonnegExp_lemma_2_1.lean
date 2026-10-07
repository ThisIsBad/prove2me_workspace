import Mathlib
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale

namespace BurkholderDFI.NonnegExp
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

/-- Lemma 2.1, p. 21. -/
theorem lemma_2_1 {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℕ mΩ} {f : ℕ → Ω → ℝ}
    (hf : Martingale f ℱ P ∨ (Submartingale f ℱ P ∧ ∀ n, 1 ≤ n → 0 ≤ᵐ[P] f n))
    (hL1 : BurkholderDFI.SquareFnLp.pNorm P 1 f < ⊤) (fInf : Ω → ℝ)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n => f n ω) atTop (𝓝 (fInf ω)))
    (l : ℝ) (hl : 0 < l) :
    (∫⁻ ω, BurkholderDFI.SquareFnLp.sqFnAt f (BurkholderDFI.SquareFnLp.exitTime f l ω - 1) ω ^ 2 ∂P
        + ∫⁻ ω, ENNReal.ofReal (BurkholderDFI.SquareFnLp.valAt f fInf (BurkholderDFI.SquareFnLp.exitTime f l ω - 1) ω ^ 2) ∂P
      ≤ ENNReal.ofReal (2 * ∫ ω, BurkholderDFI.SquareFnLp.valAt f fInf (BurkholderDFI.SquareFnLp.exitTime f l ω) ω
                                 * BurkholderDFI.SquareFnLp.valAt f fInf (BurkholderDFI.SquareFnLp.exitTime f l ω - 1) ω ∂P)) ∧
    (2 * ∫ ω, BurkholderDFI.SquareFnLp.valAt f fInf (BurkholderDFI.SquareFnLp.exitTime f l ω) ω * BurkholderDFI.SquareFnLp.valAt f fInf (BurkholderDFI.SquareFnLp.exitTime f l ω - 1) ω ∂P
      ≤ 2 * l * (BurkholderDFI.SquareFnLp.pNorm P 1 f).toReal) ∧
    (Martingale f ℱ P →
      ∫⁻ ω, BurkholderDFI.SquareFnLp.sqFnAt f (BurkholderDFI.SquareFnLp.exitTime f l ω - 1) ω ^ 2 ∂P
          + ∫⁻ ω, ENNReal.ofReal (BurkholderDFI.SquareFnLp.valAt f fInf (BurkholderDFI.SquareFnLp.exitTime f l ω - 1) ω ^ 2) ∂P
        = ENNReal.ofReal (2 * ∫ ω, BurkholderDFI.SquareFnLp.valAt f fInf (BurkholderDFI.SquareFnLp.exitTime f l ω) ω
                                   * BurkholderDFI.SquareFnLp.valAt f fInf (BurkholderDFI.SquareFnLp.exitTime f l ω - 1) ω ∂P)) := by sorry

end BurkholderDFI.NonnegExp

