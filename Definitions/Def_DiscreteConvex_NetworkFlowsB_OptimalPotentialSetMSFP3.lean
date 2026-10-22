import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsB_OptimalFlowMCFP3
import Definitions.Def_DiscreteConvex_NetworkFlowsB_IsOptimalPotential

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- The set of optimal potentials for MSFP3, `Π* = {p | p optimal potential}`. -/
def OptimalPotentialSetMSFP3 (tail head : A → V) (fa : A → ℝ → WithTop ℝ)
    (f : (V → ℝ) → WithTop ℝ) : Set (V → ℝ) :=
  {p | ∃ xi, OptimalFlowMCFP3 tail head fa f xi ∧ IsOptimalPotential tail head fa f xi p}

-- ===== MCFP0 (linear arc cost, as a special case of MCFP3, Eq. (9.11)) =====

end DiscreteConvex.NetworkFlowsB
