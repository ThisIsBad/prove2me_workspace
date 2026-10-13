import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.139, Proposition 6.8(1), in `DiscreteConvex.MConvexFunctionsB`.
-/

namespace DiscreteConvex.MConvexFunctionsB

/-- The quadratic form `f(x) = ½xᵀAx`, restricted to `\{x : Σx(i) = r\}` (`+∞` elsewhere). -/
noncomputable def QuadraticFormRestricted (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (r : ℤ) :
    (Fin n → ℤ) → WithTop ℝ :=
  fun x => if ∑ i, x i = r then
      (((1 / 2 : ℝ) * dotProduct (fun i => (x i : ℝ)) (A.mulVec (fun i => (x i : ℝ))) : ℝ) :
        WithTop ℝ)
    else ⊤

end DiscreteConvex.MConvexFunctionsB
