import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.95, Eq. (3.68): the class `C[Z→R]` of
univariate discrete convex functions, in `DiscreteConvex.IntegralConvexityC`.
-/

namespace DiscreteConvex.IntegralConvexityC

/-- `φ ∈ C[Z→R]` (Eq. (3.68)): `dom_Z φ ≠ ∅` and `φ(t-1) + φ(t+1) ≥ 2φ(t)` for all `t`
(written `φ(t)+φ(t)` to avoid scalar multiplication on `WithTop ℝ`). -/
def UnivDiscreteConvex (phi : ℤ → WithTop ℝ) : Prop :=
  (∃ t, phi t ≠ ⊤) ∧ ∀ t : ℤ, phi (t - 1) + phi (t + 1) ≥ phi t + phi t

end DiscreteConvex.IntegralConvexityC
