import Mathlib

namespace CalibratedCE.Forecast

/-- `p` is a probability vector on the finite set `α`: nonnegative entries summing to `1`. -/
def IsDist {α : Type} [Fintype α] (p : α → ℝ) : Prop :=
  (∀ a, 0 ≤ p a) ∧ ∑ a, p a = 1

end CalibratedCE.Forecast
