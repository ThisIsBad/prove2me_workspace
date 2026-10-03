import Mathlib

namespace DiscreteConvex.AlgorithmsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `ρ_p(X) = g(p+χ_X) - g(p)`, Eq. (10.32). -/
def RhoP (g : (V → ℤ) → WithTop ℝ) (p : V → ℤ) (X : Finset V) : WithTop ℝ :=
  g (fun v => p v + (if v ∈ X then (1:ℤ) else 0)) - g p

-- ===== Domain-size measures for L-convex functions (§10.3.1) =====

end DiscreteConvex.AlgorithmsC
