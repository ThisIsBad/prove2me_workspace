import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_PosScalarMul
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_SortedValues
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_ThresholdSet

namespace DiscreteConvex.LConvexFunctionsD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The Lovász extension `ρ̂ : Rⱽ → R∪{±∞}` of a set function `ρ`. -/
noncomputable def LovaszExtension (rho : Finset V → WithTop ℝ) (p : V → ℝ) : WithTop ℝ :=
  let vals := SortedValues p
  let m := vals.length
  (∑ i ∈ Finset.range (m - 1),
      PosScalarMul (vals.getD i 0 - vals.getD (i + 1) 0) (rho (ThresholdSet p (i + 1)))) +
    PosScalarMul (vals.getD (m - 1) 0) (rho (ThresholdSet p m))

end DiscreteConvex.LConvexFunctionsD
