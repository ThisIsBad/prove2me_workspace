import Mathlib
import Definitions.Def_TalagrandConc_Penalties_Basic

open MeasureTheory

namespace TalagrandConc.Penalties

theorem proposition_2_4_2
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω → Ω → ℝ) (h_nonneg : ∀ x y, 0 ≤ h x y) (h_diag : ∀ x, h x x = 0)
    (h_meas : Measurable (Function.uncurry h))
    (t : ℝ) (ht : 0 < t)
    (g : Ω → ℝ) (g_nonneg : ∀ x, 0 ≤ g x) (g_meas : Measurable g)
    (ghat_meas : Measurable (ghat t h g)) :
    (∫⁻ x, ENNReal.ofReal (Real.exp (ghat t h g x)) ∂μ) *
        (∫⁻ x, ENNReal.ofReal (Real.exp (-g x)) ∂μ)
      ≤ (1 / 2 : ENNReal) * ∫⁻ p : Ω × Ω,
          ENNReal.ofReal (Real.exp (t * vmax h p.1 p.2) + Real.exp (-(t * vmax h p.1 p.2)))
            ∂(μ.prod μ) := by sorry

end TalagrandConc.Penalties

