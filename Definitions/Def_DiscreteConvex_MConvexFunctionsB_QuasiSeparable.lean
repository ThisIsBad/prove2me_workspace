import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.140, Eq. (6.32), in `DiscreteConvex.MConvexFunctionsB`.
-/

namespace DiscreteConvex.MConvexFunctionsB

/-- A **quasi-separable convex function**, Eq. (6.32): `f(x) = f₀(Σx(i)) + Σfᵢ(x(i))`. -/
def QuasiSeparable {W : Type*} [Fintype W] (f0 : ℤ → WithTop ℝ) (fi : W → ℤ → WithTop ℝ) :
    (W → ℤ) → WithTop ℝ :=
  fun x => f0 (∑ v, x v) + ∑ v, fi v (x v)

end DiscreteConvex.MConvexFunctionsB
