import Mathlib

/-!
The standard embedding of integer vectors into real vectors, in
`DiscreteConvex.IntegralConvexityB`.
-/

namespace DiscreteConvex.IntegralConvexityB

/-- The embedding `Zⱽ ↪ Rⱽ`. -/
def EmbedZR {V : Type*} (x : V → ℤ) : V → ℝ :=
  fun v => (x v : ℝ)

end DiscreteConvex.IntegralConvexityB
