import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_KellyStochasticNetworks_Congestion

namespace KellyStochasticNetworks

/-- The objective of the **weighted α-fair** allocation problem, written in the variables
`X_r = n_r x_r` of problem (8.4):
`G(X) = ∑_r w_r n_r^α X_r^{1-α}/(1-α)` for `α ≠ 1`, and `∑_r w_r n_r log X_r` for `α = 1`.
Kelly–Yudovina, *Stochastic Networks*, pp. 188 and 190. -/
noncomputable def alphaFairObjective {R : ℕ} (w n : Fin R → ℝ) (α : ℝ) (X : Fin R → ℝ) : ℝ :=
  if α = 1 then ∑ r, w r * n r * Real.log (X r)
  else ∑ r, w r * n r ^ α * (X r ^ (1 - α) / (1 - α))

end KellyStochasticNetworks
