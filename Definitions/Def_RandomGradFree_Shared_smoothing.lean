import Mathlib

namespace RandomGradFree.Shared

open MeasureTheory ProbabilityTheory

/-- Gaussian approximation (Nesterov–Spokoiny, Eq. (9)):
`f_μ(x) = E_u f(x + μ u)` with `u` a standard Gaussian vector of `E`. -/
noncomputable def smoothing {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (f : E → ℝ) (μ : ℝ) (x : E) : ℝ :=
  ∫ u, f (x + μ • u) ∂(stdGaussian E)

end RandomGradFree.Shared
