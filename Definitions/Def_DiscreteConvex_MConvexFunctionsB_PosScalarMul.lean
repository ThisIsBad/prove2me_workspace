import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, supporting Theorem 6.13(1), in `DiscreteConvex.MConvexFunctionsB`.
-/

namespace DiscreteConvex.MConvexFunctionsB

/-- Scalar multiple of an extended real by a positive real, with the convention `c • ⊤ = ⊤`
for `c ≠ 0` and `0 • ⊤ = 0`. -/
noncomputable def PosScalarMul (c : ℝ) (x : WithTop ℝ) : WithTop ℝ :=
  match x with
  | ⊤ => if c = 0 then (0 : WithTop ℝ) else ⊤
  | (r : ℝ) => ((c * r : ℝ) : WithTop ℝ)

end DiscreteConvex.MConvexFunctionsB
