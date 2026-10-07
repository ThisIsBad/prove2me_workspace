import Mathlib
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale

namespace BurkholderDFI.SquareFnLp

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

theorem doob_1_1 {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℕ mΩ} {f : ℕ → Ω → ℝ}
    (hf : Martingale f ℱ P ∨ (Submartingale f ℱ P ∧ ∀ n, 1 ≤ n → 0 ≤ᵐ[P] f n))
    (n : ℕ) (hn : 1 ≤ n) (l : ℝ) (hl : 0 < l) :
    ENNReal.ofReal l * P {ω | ENNReal.ofReal l < maxFnN f n ω}
        ≤ ∫⁻ ω in {ω | ENNReal.ofReal l < maxFnN f n ω}, ENNReal.ofReal |f n ω| ∂P ∧
      ∫⁻ ω in {ω | ENNReal.ofReal l < maxFnN f n ω}, ENNReal.ofReal |f n ω| ∂P ≤ pNorm P 1 f := by sorry

end BurkholderDFI.SquareFnLp

