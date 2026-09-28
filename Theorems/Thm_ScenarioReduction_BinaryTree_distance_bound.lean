import Mathlib
import Definitions.Def_ScenarioReduction_BinaryTree_scenario

namespace ScenarioReduction.BinaryTree

theorem distance_bound (K : ℕ) (δ : ℕ → ℝ) (hδ : ∀ k ∈ Finset.Icc 1 K, 0 ≤ δ k)
    (k0 : ℕ) (hk0 : k0 ∈ Finset.Icc 1 K) (hmin : ∀ k ∈ Finset.Icc 1 K, δ k0 ≤ δ k)
    (σ τ : Fin K → Fin 2) (l : ℕ) (hl : l ∈ Finset.Icc 1 K) (hdiff : lev σ l ≠ lev τ l)
    (hagree : ∀ r ∈ Finset.Icc 1 (l - 1), lev σ r = lev τ r) :
    2 * δ l ≤ ‖scenario δ σ - scenario δ τ‖ ∧ 2 * δ k0 ≤ ‖scenario δ σ - scenario δ τ‖ := by sorry

end ScenarioReduction.BinaryTree

