import Mathlib
import Definitions.Def_RandomGradFree_Shared_smoothing

open MeasureTheory ProbabilityTheory

namespace RandomGradFree.Smooth

theorem smoothing_convex {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : E → ℝ) (hf : ConvexOn ℝ Set.univ f)
    (μ : ℝ) (hμ : 0 ≤ μ)
    (hint : ∀ x, Integrable (fun u => f (x + μ • u)) (stdGaussian E)) :
    ConvexOn ℝ Set.univ (RandomGradFree.Shared.smoothing f μ) := by sorry

end RandomGradFree.Smooth
