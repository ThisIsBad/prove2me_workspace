import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.148-149: the minimizer set of a function on
the integer lattice, in `DiscreteConvex.MConvexFunctions`.
-/

namespace DiscreteConvex.MConvexFunctions

/-- The minimizer set `arg min f = \{x ∈ Zⱽ : f(x) ≤ f(y)\ ∀y ∈ Zⱽ\}`. -/
def ArgMin {V : Type*} (f : (V → ℤ) → WithTop ℝ) : Set (V → ℤ) :=
  {x | ∀ y, f x ≤ f y}

end DiscreteConvex.MConvexFunctions
