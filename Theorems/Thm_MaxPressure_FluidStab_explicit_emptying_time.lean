import Mathlib
import Definitions.Def_MaxPressure_FluidStab_Network

namespace MaxPressure.FluidStab

open Matrix

/-- Proof of Theorem 5, App. B, p. 215 (last line): under Assumptions 1 and 2, if the LP (9)–(13)
has a feasible solution with `ρ < 1`, there is `ε > 0` (the paper's `δ`) such that every maximum
pressure fluid model solution has `Z̄(t) = 0` for `t ≥ ‖Z̄(0)‖/ε`. -/
theorem explicit_emptying_time {I J K : ℕ} (N : Network I J K) (hN : N.Standing)
    (hEAA : EAA N) (h2 : Assumption2 N)
    (hLP : ∃ (x : Fin J → ℝ) (ρ : ℝ), ρ < 1 ∧ LPFeasible N x ρ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (Zb : ℝ → Fin I → ℝ) (Tb : ℝ → Fin J → ℝ),
      IsFluidSolution N Zb Tb → MPFluidEq N Zb Tb →
      ∀ t, Real.sqrt (∑ i, Zb 0 i ^ 2) / ε ≤ t → Zb t = 0 := by sorry

end MaxPressure.FluidStab

