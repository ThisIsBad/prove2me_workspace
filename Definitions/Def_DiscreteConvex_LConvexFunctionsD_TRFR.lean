import Mathlib

namespace DiscreteConvex.LConvexFunctionsD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Axiom (TRF[R]): `∃r, g(p+α1) = g(p)+αr` for all `p ∈ Rⱽ, α ∈ R`. -/
def TRFR (g : (V → ℝ) → WithTop ℝ) : Prop :=
  ∃ r : ℝ, ∀ p : V → ℝ, ∀ alpha : ℝ, g (fun v => p v + alpha) = g p + (alpha * r : WithTop ℝ)

end DiscreteConvex.LConvexFunctionsD
