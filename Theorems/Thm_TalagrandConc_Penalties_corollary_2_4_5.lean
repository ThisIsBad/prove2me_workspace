import Mathlib
import Definitions.Def_TalagrandConc_Penalties_Basic

open MeasureTheory

namespace TalagrandConc.Penalties

theorem corollary_2_4_5
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω → Ω → ℝ) (h_nonneg : ∀ x y, 0 ≤ h x y) (h_diag : ∀ x, h x x = 0)
    (h_meas : Measurable (Function.uncurry h))
    (h_sup_fin : (⨆ x, ⨆ y, ENNReal.ofReal (h x y)) ≠ ⊤)
    (N : ℕ) (A : Set (Fin N → Ω)) (hA : MeasurableSet A) (hfA : Measurable (fh h A))
    (u : ℝ) :
    (Measure.pi fun _ : Fin N => μ) {x | ENNReal.ofReal u ≤ fh h A x}
      ≤ if (Measure.pi fun _ : Fin N => μ) A = 0 then ⊤ else
        ((Measure.pi fun _ : Fin N => μ) A)⁻¹ *
        EReal.exp (-((min
          (ENNReal.ofReal (u ^ 2) /
            (8 * (N : ENNReal) * ∫⁻ p : Ω × Ω, ENNReal.ofReal (h p.1 p.2 ^ 2) ∂(μ.prod μ)))
          (ENNReal.ofReal u / (2 * ⨆ x, ⨆ y, ENNReal.ofReal (h x y))) : ENNReal) : EReal)) := by sorry

end TalagrandConc.Penalties

