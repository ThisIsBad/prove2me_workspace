import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.143, Eq. (6.46), in `DiscreteConvex.MConvexFunctionsB`.
-/

namespace DiscreteConvex.MConvexFunctionsB

/-- The separable perturbation `f̃(x) = f(x) + Σᵥ ϕᵥ(x(v))`, Eq. (6.46). -/
def SeparablePerturb {V : Type*} [Fintype V] (f : (V → ℤ) → WithTop ℝ) (phi : V → ℤ → WithTop ℝ) :
    (V → ℤ) → WithTop ℝ :=
  fun x => f x + ∑ v, phi v (x v)

end DiscreteConvex.MConvexFunctionsB
