import Mathlib
import Definitions.Def_ScenarioReduction_BinaryTree_redCost

namespace ScenarioReduction.BinaryTree

theorem three_quarter_solution (K : ℕ) (δ : ℕ → ℝ) (hδ : ∀ k ∈ Finset.Icc 1 K, 0 ≤ δ k)
    (hK : 3 ≤ K) (k0 : ℕ) (hk0 : k0 ∈ Finset.Icc 1 K)
    (hmin : ∀ k ∈ Finset.Icc 1 K, δ k0 ≤ δ k) (hk0K : k0 ≤ K - 2)
    (hmax : max (δ (k0 + 1)) (δ (k0 + 2)) ≤ 2 * δ k0) :
    (∀ σ τ : Fin K → Fin 2, σ ≠ τ → 2 * δ k0 ≤ ‖scenario δ σ - scenario δ τ‖) ∧
    (∃ Jstar : Finset (Fin K → Fin 2), Jstar.card = 3 * 2 ^ (K - 2) ∧
      ∀ j ∈ Jstar, ∃ i ∉ Jstar, ‖scenario δ i - scenario δ j‖ = 2 * δ k0) ∧
    (∀ n : ℕ, 2 ^ K ≤ 4 * n → n < 2 ^ K →
      IsLeast {v : ℝ | ∃ J : Finset (Fin K → Fin 2), J.card = 2 ^ K - n ∧
          ∃ hJ : Jᶜ.Nonempty, v = redCost δ J hJ}
        (((2 : ℝ) ^ K - n) / 2 ^ K * (2 * δ k0))) := by sorry

end ScenarioReduction.BinaryTree

