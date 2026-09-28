import Mathlib
import Definitions.Def_ScenarioReduction_TernaryTree_scenario
import Definitions.Def_ScenarioReduction_TernaryTree_redCost

namespace ScenarioReduction.TernaryTree

theorem seven_ninths_solution (K : ℕ) (hK : 3 ≤ K) (δ : ℕ → ℝ)
    (hδ : ∀ k ∈ Finset.Icc 1 K, 0 ≤ δ k)
    (k0 : ℕ) (hk0 : k0 ∈ Finset.Icc 1 K) (hmin : ∀ k ∈ Finset.Icc 1 K, δ k0 ≤ δ k)
    (hk0K : k0 ≤ K - 2) (hmax : max (δ (k0 + 1)) (δ (k0 + 2)) ≤ 2 * δ k0) :
    (∀ σ τ : Fin K → Fin 3, σ ≠ τ → δ k0 ≤ ‖scenario δ σ - scenario δ τ‖) ∧
    (∃ Jss : Finset (Fin K → Fin 3), Jss.card = 7 * 3 ^ (K - 2) ∧
      ∀ j ∈ Jss, ∃ i ∉ Jss, ‖scenario δ i - scenario δ j‖ = δ k0) ∧
    (∀ n : ℕ, 2 * 3 ^ K ≤ 9 * n → n < 3 ^ K →
      IsLeast {x : ℝ | ∃ (J : Finset (Fin K → Fin 3)) (hJ : Jᶜ.Nonempty), J.card = 3 ^ K - n ∧
          x = redCost (fun _ => 1 / (3 : ℝ) ^ K)
            (fun i j => ‖scenario δ i - scenario δ j‖) J hJ}
        (((3 : ℝ) ^ K - n) / 3 ^ K * δ k0)) := by sorry

end ScenarioReduction.TernaryTree

