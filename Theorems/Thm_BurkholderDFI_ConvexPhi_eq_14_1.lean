import Mathlib
import Definitions.Def_BurkholderDFI_ConvexPhi_Davis

namespace BurkholderDFI.ConvexPhi
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- (14.1), p. 33: Davis's decomposition into two martingales. -/
theorem eq_14_1 {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ℱ : Filtration ℕ mΩ} {f : ℕ → Ω → ℝ}
    (hf : Martingale f ℱ P) :
    Martingale (fun n => if n = 0 then (fun _ => (0 : ℝ)) else davisG ℱ P f n) ℱ P ∧
    Martingale (fun n => if n = 0 then f 0 else davisH ℱ P f n) ℱ P ∧
    ∀ n, 1 ≤ n → ∀ ω, f n ω = davisG ℱ P f n ω + davisH ℱ P f n ω := by sorry
end BurkholderDFI.ConvexPhi

