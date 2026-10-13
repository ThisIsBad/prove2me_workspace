import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.139, Proposition 6.8(2), in `DiscreteConvex.MConvexFunctionsB`.
-/

namespace DiscreteConvex.MConvexFunctionsB

/-- The quadratic form `f(x) = ½xᵀAx`, defined on all of `Zⁿ`. -/
noncomputable def QuadraticFormTotal (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) : (Fin n → ℤ) → WithTop ℝ :=
  fun x => (((1 / 2 : ℝ) * dotProduct (fun i => (x i : ℝ)) (A.mulVec (fun i => (x i : ℝ))) : ℝ) :
    WithTop ℝ)

end DiscreteConvex.MConvexFunctionsB
