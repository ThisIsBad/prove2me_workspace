import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.79, Eq. (3.14): the epigraph of a function, in
`DiscreteConvex.IntegralConvexityB`.
-/

namespace DiscreteConvex.IntegralConvexityB

/-- `epi f = \{(x,Y) ∈ Rⁿ⁺¹ | Y ≥ f(x)\}` (Eq. (3.14)). -/
def Epi {V : Type*} (f : (V → ℝ) → EReal) : Set ((V → ℝ) × ℝ) :=
  {p | (p.2 : EReal) ≥ f p.1}

end DiscreteConvex.IntegralConvexityB
