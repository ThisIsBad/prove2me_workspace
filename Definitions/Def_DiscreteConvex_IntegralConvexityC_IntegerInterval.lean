import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.92, Eq. (3.54): the integer interval, in
`DiscreteConvex.IntegralConvexityC`.
-/

namespace DiscreteConvex.IntegralConvexityC

/-- The integer interval `[a,b] = \{x ∈ Zⁿ : a(i) ≤ x(i) ≤ b(i)\}` (Eq. (3.54)), finite
endpoints. -/
def IntegerInterval {n : ℕ} (a b : Fin n → ℤ) : Set (Fin n → ℤ) :=
  {x | ∀ i, a i ≤ x i ∧ x i ≤ b i}

end DiscreteConvex.IntegralConvexityC
