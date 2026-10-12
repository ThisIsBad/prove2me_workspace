import Mathlib
import Definitions.Def_BoundedNV_Pooling_Logit

open MeasureTheory

namespace BoundedNV.Pooling

/-- Lemma 2, p. 572: a common additive shift of utility preserves the choice CDF. -/
theorem lemma2_additive_invariance (Y : Set ℝ) (u : ℝ → ℝ) (β a : ℝ)
    (hY : MeasurableSet Y)
    (hu : IntegrableOn (fun v => Real.exp (u v / β)) Y)
    (hZ : 0 < ∫ v in Y, Real.exp (u v / β))
    (hβ : 0 < β) (y : ℝ) :
    logitCDF Y (fun v => u v + a) β y = logitCDF Y u β y := by sorry

end BoundedNV.Pooling

