import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.143, Eq. (6.40), in `DiscreteConvex.MConvexFunctionsB`.
-/

namespace DiscreteConvex.MConvexFunctionsB

/-- The restriction `f_U` of `f` to `U ⊆ V` (Eq. (6.40)), represented as vectors vanishing
outside `U`. -/
def Restriction {V : Type*} [Fintype V] [DecidableEq V] (f : (V → ℤ) → WithTop ℝ) (U : Finset V) :
    (V → ℤ) → WithTop ℝ :=
  fun y => if (∀ v ∉ U, y v = 0) then f y else ⊤

end DiscreteConvex.MConvexFunctionsB
