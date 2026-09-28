import Mathlib

namespace GoldenRatioVI.Shared

/-- `x̄` is the proximal point of `g` at `z`, i.e. `x̄ ∈ argmin_x {g x + ½‖x - z‖²}`:
`g x̄ + ½‖x̄ - z‖² ≤ g x + ½‖x - z‖²` for every `x` (in `EReal`).
Existence and uniqueness of `x̄` for proper convex lsc `g` are theorems, not part of
this predicate. -/
def IsProxPoint {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : E → EReal) (z xbar : E) : Prop :=
  ∀ x : E, g xbar + ((‖xbar - z‖ ^ 2 / 2 : ℝ) : EReal) ≤ g x + ((‖x - z‖ ^ 2 / 2 : ℝ) : EReal)

end GoldenRatioVI.Shared
