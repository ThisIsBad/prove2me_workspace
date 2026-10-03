import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.93, Eq. (3.58): the integral neighborhood
`N(x)`, in `DiscreteConvex.IntegralConvexityC`.
-/

namespace DiscreteConvex.IntegralConvexityC

/-- `N(x) = \{y ∈ Zⁿ : ⌊x_i⌋ ≤ y_i ≤ ⌈x_i⌉\}` (Eq. (3.58)). -/
def IntegralNeighborhood {n : ℕ} (x : Fin n → ℝ) : Set (Fin n → ℤ) :=
  {y | ∀ i, ⌊x i⌋ ≤ y i ∧ y i ≤ ⌈x i⌉}

end DiscreteConvex.IntegralConvexityC
