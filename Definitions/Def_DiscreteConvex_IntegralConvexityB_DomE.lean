import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.97, Eq. (3.3): the effective domain of a
function, in `DiscreteConvex.IntegralConvexityB`.
-/

namespace DiscreteConvex.IntegralConvexityB

/-- `dom f = \{x | -∞ < f(x) < +∞\}` (Eq. (3.3)). -/
def DomE {V : Type*} (f : (V → ℝ) → EReal) : Set (V → ℝ) :=
  {x | f x ≠ ⊤ ∧ f x ≠ ⊥}

end DiscreteConvex.IntegralConvexityB
