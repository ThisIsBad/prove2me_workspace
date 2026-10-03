import Mathlib
import Definitions.Def_ProcessingNetworks_LyapunovCriteria_LipschitzOn
import Definitions.Def_ProcessingNetworks_LyapunovCriteria_FluidEquationData

namespace ProcessingNetworks.LyapunovCriteria

/-- Lemma 8.3, Dai & Harrison p. 136 (PDF p. 152): any solution `(D, F, T, Z)` of the fluid
equations (6.1)-(6.6) is globally Lipschitz (on `ℝ_+`, each component). -/
theorem fluid_model_solution_globally_lipschitz
    {I J K : ℕ} (dat : FluidEquationData I J K)
    (hA : ∀ k j, 0 ≤ dat.A k j) (hAcol : ∀ j, ∃ k, 0 < dat.A k j)
    (Dh : ℝ → Fin I → ℝ) (Fh Th : ℝ → Fin J → ℝ) (Zh : ℝ → Fin I → ℝ)
    (hsol : IsFluidModelSolution dat Dh Fh Th Zh) :
    IsGloballyLipschitzOn Dh (Set.Ici (0 : ℝ)) ∧ IsGloballyLipschitzOn Fh (Set.Ici (0 : ℝ)) ∧
    IsGloballyLipschitzOn Th (Set.Ici (0 : ℝ)) ∧ IsGloballyLipschitzOn Zh (Set.Ici (0 : ℝ)) := by sorry

end ProcessingNetworks.LyapunovCriteria
