import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.107, Eq. (3.45): the dual LP feasible region,
in `DiscreteConvex.IntegralConvexityB`.
-/

namespace DiscreteConvex.IntegralConvexityB

/-- `D = \{y ∈ Rᵐ | Aᵀy ≤ c\}` (Eq. (3.45)), stated as `y⊤A ≤ c⊤` via `Matrix.vecMul`. -/
def DualFeas {V W : Type*} [Fintype W] (A : Matrix W V ℝ) (c : V → ℝ) : Set (W → ℝ) :=
  {y | ∀ j, Matrix.vecMul y A j ≤ c j}

end DiscreteConvex.IntegralConvexityB
