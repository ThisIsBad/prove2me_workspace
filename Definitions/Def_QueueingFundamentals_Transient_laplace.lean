import Mathlib

namespace QueueingFundamentals.Transient

open MeasureTheory

/-- The Laplace transform `f̄(s) = ∫_0^∞ e^{-st} f(t) dt` of a real function `f` on `[0, ∞)`, at a
complex argument `s` (p.99). It is a Bochner integral over `(0, ∞)`; statements that use it state
the integrability they need. -/
noncomputable def laplace (f : ℝ → ℝ) (s : ℂ) : ℂ :=
  ∫ t in Set.Ioi (0 : ℝ), Complex.exp (-s * (t : ℂ)) * (f t : ℂ)

end QueueingFundamentals.Transient
