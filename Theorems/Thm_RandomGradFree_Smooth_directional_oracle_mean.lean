import Mathlib

open MeasureTheory ProbabilityTheory

namespace RandomGradFree.Smooth

theorem directional_oracle_mean {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : E → ℝ) (x : E) (hfx : DifferentiableAt ℝ f x) :
    ∫ u, fderiv ℝ f x u • u ∂(stdGaussian E) = gradient f x := by sorry

end RandomGradFree.Smooth
