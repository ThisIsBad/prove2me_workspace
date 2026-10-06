import Mathlib

/-!
The integer points `Zⱽ` viewed as a subset of `Rⱽ`, used throughout this mission (Murota,
*Discrete Convex Analysis*, SIAM 2003, pp.107-116), in `DiscreteConvex.MConvexSetsB`.
-/

namespace DiscreteConvex.MConvexSetsB

/-- The integer points of `Rⱽ`: `\{x : ∀v, ∃k:ℤ, x(v)=k\}`. -/
def IntPts {V : Type*} : Set (V → ℝ) :=
  {x : V → ℝ | ∀ v, ∃ k : ℤ, x v = (k : ℝ)}

end DiscreteConvex.MConvexSetsB
