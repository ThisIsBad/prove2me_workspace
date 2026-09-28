import Mathlib
import Definitions.Def_ScenarioReduction_TernaryTree_scenario
import Definitions.Def_ScenarioReduction_TernaryTree_redCost

namespace ScenarioReduction.TernaryTree

theorem example_4_2 (δ : ℕ → ℝ)
    (hδ : δ 1 = 0.7 ∧ δ 2 = 0.9 ∧ δ 3 = 1.2 ∧ δ 4 = 1.5 ∧ δ 5 = 2.6 ∧ δ 6 = 3.3)
    (n : ℕ) (hn : 162 ≤ n) (hnN : n < 729) :
    IsLeast {x : ℝ | ∃ (J : Finset (Fin 6 → Fin 3)) (hJ : Jᶜ.Nonempty), J.card = 729 - n ∧
        x = redCost (fun _ => 1 / (729 : ℝ))
          (fun i j => ‖scenario δ i - scenario δ j‖) J hJ}
      (0.7 * ((729 : ℝ) - n) / 729) := by sorry

end ScenarioReduction.TernaryTree

