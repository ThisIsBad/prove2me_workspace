import Mathlib
import Definitions.Def_MaxPressure_Throughput_Network

namespace MaxPressure.Throughput

/-- Theorem 4, p. 203: an LP-feasible maximum-pressure fluid model is
weakly stable under Assumption 1. -/
theorem mp_fluid_weak_stability {I J K : ℕ} (N : Network I J K)
    (hN : N.Standing) (hEAA : EAA N)
    (hlp : ∃ x rho, rho ≤ (1 : ℝ) ∧ LPFeasible N x rho) :
    WeaklyStable (fun Zb Tb => IsFluidSolution N Zb Tb ∧ MPFluidEq N Zb Tb) := by sorry

end MaxPressure.Throughput

