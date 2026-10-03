import Mathlib

namespace DiscreteConvex.LConvexFunctionsD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The set function `ρ_g(X) = g(χ_X)` induced by a positively homogeneous real-domain
function, Eq. (7.35). -/
def InducedRho (g : (V → ℝ) → WithTop ℝ) (X : Finset V) : WithTop ℝ :=
  g (fun v => if v ∈ X then (1 : ℝ) else 0)

end DiscreteConvex.LConvexFunctionsD
