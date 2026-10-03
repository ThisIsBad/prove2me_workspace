import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsB_OptimalFlowMSFP3Z
import Definitions.Def_DiscreteConvex_NetworkFlowsB_IsOptimalPotentialZ

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- The set of integer-valued optimal potentials for MSFP3. -/
def OptimalPotentialSetZ (tail head : A → V) (fa : A → ℤ → WithTop ℝ) (f : (V → ℤ) → WithTop ℝ) :
    Set (V → ℤ) :=
  {pZ | ∃ xi, OptimalFlowMSFP3Z tail head fa f xi ∧
    IsOptimalPotentialZ tail head fa f xi (fun v => (pZ v : ℝ))}

end DiscreteConvex.NetworkFlowsB
