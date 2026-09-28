import Mathlib
import Definitions.Def_ScenarioReduction_BinaryTree_scenario

namespace ScenarioReduction.BinaryTree

/-- Reduction cost of eq. (8) for the regular binary tree with `N = 2^K` scenarios,
uniform weights `p_i = 1/N`, and `c(ω, ω̃) = ‖ω - ω̃‖_∞` (Mathlib's norm on `Fin (K+1) → ℝ`
is the sup norm):
`D_J = ∑_{i ∈ J} p_i min_{j ∉ J} ‖ω_i - ω_j‖_∞`, for a set `J` of deleted scenarios whose
complement is nonempty. -/
noncomputable def redCost {K : ℕ} (δ : ℕ → ℝ) (J : Finset (Fin K → Fin 2))
    (hJ : Jᶜ.Nonempty) : ℝ :=
  ∑ σ ∈ J, (1 / (2 ^ K : ℝ)) * Jᶜ.inf' hJ (fun τ => ‖scenario δ σ - scenario δ τ‖)

end ScenarioReduction.BinaryTree
