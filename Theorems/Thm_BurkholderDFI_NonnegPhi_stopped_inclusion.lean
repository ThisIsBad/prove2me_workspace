import Mathlib
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace BurkholderDFI.NonnegPhi

/-- §18, proof of Theorem 18.2, p. 37: with `μ = inf {n : |f_n| > δλ}`,
`P(S(f) > βλ, f^* ≤ δλ) ≤ P(S_{μ−1}(f) > βλ)`. -/
theorem stopped_inclusion {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (f : ℕ → Ω → ℝ)
    (β δ l : ℝ) (hδ : 0 < δ) (hl : 0 < l) :
    P {ω | ENNReal.ofReal (β * l) < BurkholderDFI.SquareFnLp.sqFn f ω ∧ BurkholderDFI.SquareFnLp.maxFn f ω ≤ ENNReal.ofReal (δ * l)}
      ≤ P {ω | ENNReal.ofReal (β * l) < BurkholderDFI.SquareFnLp.sqFnAt f (BurkholderDFI.SquareFnLp.exitTime f (δ * l) ω - 1) ω} := by sorry

end BurkholderDFI.NonnegPhi

