import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_DiscreteConvexUnivariate

namespace DiscreteConvex.ConjugacyDualityD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `f` is separable convex: `f(x) = Σ_v ψ_v(x(v))` for univariate discrete-convex `ψ_v`. -/
def IsSeparableConvex (f : (V → ℤ) → WithTop ℝ) : Prop :=
  ∃ psi : V → ℤ → WithTop ℝ, (∀ v, DiscreteConvexUnivariate (psi v)) ∧
    ∀ x, f x = ∑ v, psi v (x v)

end DiscreteConvex.ConjugacyDualityD
