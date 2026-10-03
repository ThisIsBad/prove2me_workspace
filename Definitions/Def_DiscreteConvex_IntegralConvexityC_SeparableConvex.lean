import Mathlib
import Definitions.Def_DiscreteConvex_IntegralConvexityC_UnivDiscreteConvex

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.95, Eq. (3.67): a separable convex function,
in `DiscreteConvex.IntegralConvexityC`.
-/

namespace DiscreteConvex.IntegralConvexityC

/-- `f` is a **separable convex function** (Eq. (3.67)): `f(x) = ∑ᵢ fᵢ(x(i))` with each
`fᵢ ∈ C[Z→R]`. -/
def SeparableConvex {n : ℕ} (f : (Fin n → ℤ) → WithTop ℝ) : Prop :=
  ∃ fi : Fin n → ℤ → WithTop ℝ, (∀ i, UnivDiscreteConvex (fi i)) ∧
    ∀ x : Fin n → ℤ, f x = ∑ i, fi i (x i)

end DiscreteConvex.IntegralConvexityC
