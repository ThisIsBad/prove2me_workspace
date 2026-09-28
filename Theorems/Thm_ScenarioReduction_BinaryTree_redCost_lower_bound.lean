import Mathlib
import Definitions.Def_ScenarioReduction_BinaryTree_redCost

namespace ScenarioReduction.BinaryTree

theorem redCost_lower_bound (K : ℕ) (δ : ℕ → ℝ) (hδ : ∀ k ∈ Finset.Icc 1 K, 0 ≤ δ k)
    (k0 : ℕ) (hk0 : k0 ∈ Finset.Icc 1 K) (hmin : ∀ k ∈ Finset.Icc 1 K, δ k0 ≤ δ k)
    (n : ℕ) (hn : n < 2 ^ K) (J : Finset (Fin K → Fin 2)) (hJcard : J.card = 2 ^ K - n)
    (hJ : Jᶜ.Nonempty) :
    ((2 : ℝ) ^ K - n) / 2 ^ K * (2 * δ k0) ≤ redCost δ J hJ := by sorry

end ScenarioReduction.BinaryTree

