import Mathlib

namespace NetworkControl.GeneralCosts

/-- The virtual power queue recursion, Eq. (6.13), p. 114: `D(t+1) = max[D(t)-Pav,0] + Σ_i P_i(t)`,
with initial condition `D(0) = 0`. `P : ℕ → Fin L → ℝ` is the power-allocation process. -/
def virtualPowerQueue {L : ℕ} (P : ℕ → Fin L → ℝ) (Pav : ℝ) : ℕ → ℝ
  | 0 => 0
  | t + 1 => max (virtualPowerQueue P Pav t - Pav) 0 + ∑ i : Fin L, P t i

end NetworkControl.GeneralCosts
