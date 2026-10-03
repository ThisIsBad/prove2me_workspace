import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.133, in `DiscreteConvex.MConvexFunctionsB`.
-/

namespace DiscreteConvex.MConvexFunctionsB

/-- The effective domain `dom f = \{x ∈ Zⱽ : f(x) ≠ +∞\}` of `f : Zⱽ → R ∪ {+∞}`. -/
def DomZ {V : Type*} (f : (V → ℤ) → WithTop ℝ) : Set (V → ℤ) := {x | f x ≠ ⊤}

end DiscreteConvex.MConvexFunctionsB
