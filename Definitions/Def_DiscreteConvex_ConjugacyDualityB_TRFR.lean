import Mathlib

namespace DiscreteConvex.ConjugacyDualityB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Axiom (TRF[R]). -/
def TRFR (g : (V → ℝ) → WithTop ℝ) : Prop :=
  ∃ r : ℝ, ∀ p : V → ℝ, ∀ alpha : ℝ, g (fun v => p v + alpha) = g p + (alpha * r : WithTop ℝ)

end DiscreteConvex.ConjugacyDualityB
