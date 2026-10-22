import Mathlib

/-!
The embedding `R ∪ {+∞} ↪ R ∪ {±∞}`, in `DiscreteConvex.IntegralConvexityC`.
-/

namespace DiscreteConvex.IntegralConvexityC

/-- The canonical embedding `WithTop ℝ → EReal`. -/
def ToEReal3 (v : WithTop ℝ) : EReal :=
  WithBot.some v

end DiscreteConvex.IntegralConvexityC
