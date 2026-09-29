import Mathlib
import Definitions.Def_RobustGeneralization_GaussLower_Model

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RobustGeneralization.GaussLower

theorem eq2_posterior_swap (d n : ℕ) (σ : ℝ) (hσ : 0 < σ)
    (F : E d × (Fin n → E d) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ θ, ∫⁻ z, F (θ, z) ∂(Measure.pi fun _ : Fin n => gaussVec θ σ) ∂(stdGaussian (E d)) =
      ∫⁻ z, ∫⁻ θ, F (θ, z) ∂(posterior z σ) ∂(sampleMarginal d n σ) := by sorry

end RobustGeneralization.GaussLower
