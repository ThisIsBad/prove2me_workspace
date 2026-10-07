import Mathlib
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace BurkholderDFI.Gundy

/-- (1.5), p. 20: `λ^p P(f^* > λ) ≤ ‖f‖_p^p` for `1 ≤ p < ∞`, `f` a martingale or a nonnegative
submartingale. -/
theorem eq_1_5 {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℕ mΩ} {f : ℕ → Ω → ℝ}
    (hf : Martingale f ℱ P ∨ (Submartingale f ℱ P ∧ ∀ n, 1 ≤ n → 0 ≤ᵐ[P] f n))
    (p : ℝ) (hp : 1 ≤ p) (l : ℝ) (hl : 0 < l) :
    ENNReal.ofReal (l ^ p) * P {ω | ENNReal.ofReal l < BurkholderDFI.SquareFnLp.maxFn f ω} ≤ BurkholderDFI.SquareFnLp.pNorm P p f ^ p := by sorry

end BurkholderDFI.Gundy

