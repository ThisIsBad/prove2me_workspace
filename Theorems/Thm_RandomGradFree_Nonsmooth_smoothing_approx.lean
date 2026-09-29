import Mathlib
import Definitions.Def_RandomGradFree_Shared_smoothing

namespace RandomGradFree.Nonsmooth

theorem smoothing_approx {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : E → ℝ) (L₀ : ℝ) (hL₀ : 0 ≤ L₀) (hLip : ∀ x y, |f x - f y| ≤ L₀ * ‖x - y‖)
    (μ : ℝ) (hμ : 0 ≤ μ) (x : E) :
    |RandomGradFree.Shared.smoothing f μ x - f x| ≤ μ * L₀ * Real.sqrt (Module.finrank ℝ E) := by sorry

end RandomGradFree.Nonsmooth
