import Mathlib

namespace DiscreteConvex.AlgorithmsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `ϕ : V×V → R` is a `δ`-feasible flow. -/
def IsDeltaFeasibleFlow (delta : ℝ) (phi : V → V → ℝ) : Prop :=
  ∀ u v, 0 ≤ phi u v ∧ phi u v ≤ delta ∧ (phi u v = 0 ∨ phi v u = 0)

end DiscreteConvex.AlgorithmsB
