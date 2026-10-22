import Mathlib
import Definitions.Def_ShockWear_CumDamage_Model

namespace ShockWear.CumDamage

open MeasureTheory ProbabilityTheory

theorem corollary42 (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : μ (Set.Iio 0) = 0)
    (lam : ℝ) (hlam : 0 < lam) (x : ℝ) :
    IsIHRA (shockSurv lam (fun k => cdfPow μ k x)) := by sorry

end ShockWear.CumDamage

