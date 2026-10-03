import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_SortedValues

namespace DiscreteConvex.LConvexFunctionsD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The `i`-th threshold set `Uᵢ = {v ∈ V : p(v) ≥ p̂ᵢ}` (1-indexed). -/
noncomputable def ThresholdSet (p : V → ℝ) (i : ℕ) : Finset V :=
  Finset.univ.filter (fun v => (SortedValues p).getD (i - 1) 0 ≤ p v)

end DiscreteConvex.LConvexFunctionsD
