import Mathlib
import Definitions.Def_ScenarioReduction_TernaryTree_scenario
import Definitions.Def_ScenarioReduction_TernaryTree_redCost

namespace ScenarioReduction.TernaryTree

theorem redCost_lower_bound (K : ℕ) (δ : ℕ → ℝ) (hδ : ∀ k ∈ Finset.Icc 1 K, 0 ≤ δ k)
    (k0 : ℕ) (hk0 : k0 ∈ Finset.Icc 1 K) (hmin : ∀ k ∈ Finset.Icc 1 K, δ k0 ≤ δ k)
    (n : ℕ) (hn : n < 3 ^ K) (J : Finset (Fin K → Fin 3)) (hJ : Jᶜ.Nonempty)
    (hcard : J.card = 3 ^ K - n) :
    ((3 : ℝ) ^ K - n) / 3 ^ K * δ k0 ≤
      redCost (fun _ => 1 / (3 : ℝ) ^ K) (fun i j => ‖scenario δ i - scenario δ j‖) J hJ := by sorry

end ScenarioReduction.TernaryTree

