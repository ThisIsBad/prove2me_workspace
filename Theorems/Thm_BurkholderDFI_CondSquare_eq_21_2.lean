import Mathlib
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace BurkholderDFI.CondSquare

/-- (21.2), p. 39: for a martingale `f`, `β > 1` and `0 < δ < β − 1`,
`P(f^* > βλ, s(f) ∨ d^* ≤ δλ) ≤ δ²/(β − δ − 1)² · P(f^* > λ)` for every `λ > 0`. -/
theorem eq_21_2 {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℕ mΩ} {f : ℕ → Ω → ℝ} (hf : Martingale f ℱ P)
    (β δ : ℝ) (hβ : 1 < β) (hδ : 0 < δ) (hδβ : δ < β - 1) (l : ℝ) (hl : 0 < l) :
    P {ω | ENNReal.ofReal (β * l) < BurkholderDFI.SquareFnLp.maxFn f ω ∧
          max (BurkholderDFI.SquareFnLp.condSqFn ℱ P f ω) (BurkholderDFI.SquareFnLp.maxFn (BurkholderDFI.SquareFnLp.dseq f) ω) ≤ ENNReal.ofReal (δ * l)}
      ≤ ENNReal.ofReal (δ ^ 2 / (β - δ - 1) ^ 2) * P {ω | ENNReal.ofReal l < BurkholderDFI.SquareFnLp.maxFn f ω} := by sorry

end BurkholderDFI.CondSquare

