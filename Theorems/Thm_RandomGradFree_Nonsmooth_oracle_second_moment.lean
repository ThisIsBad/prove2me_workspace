import Mathlib
import Definitions.Def_RandomGradFree_Nonsmooth_oracle

open MeasureTheory ProbabilityTheory

namespace RandomGradFree.Nonsmooth

theorem oracle_second_moment {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : E → ℝ) (hf : ConvexOn ℝ Set.univ f)
    (L₀ : ℝ) (hL₀ : 0 ≤ L₀) (hLip : ∀ x y, |f x - f y| ≤ L₀ * ‖x - y‖)
    (μ : ℝ) (hμ : 0 < μ) (x : E) :
    ∫ u, ‖oracle f μ x u‖ ^ 2 ∂(stdGaussian E)
      ≤ L₀ ^ 2 * ((Module.finrank ℝ E : ℝ) + 4) ^ 2 := by sorry

end RandomGradFree.Nonsmooth
