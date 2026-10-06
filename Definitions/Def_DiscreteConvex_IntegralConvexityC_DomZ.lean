import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.93: the effective domain `dom_Z f`, in
`DiscreteConvex.IntegralConvexityC`.
-/

namespace DiscreteConvex.IntegralConvexityC

/-- `dom_Z f = \{x ∈ Zⁿ : f(x) ≠ +∞\}`. -/
def DomZ {n : ℕ} (f : (Fin n → ℤ) → WithTop ℝ) : Set (Fin n → ℤ) :=
  {x | f x ≠ ⊤}

end DiscreteConvex.IntegralConvexityC
