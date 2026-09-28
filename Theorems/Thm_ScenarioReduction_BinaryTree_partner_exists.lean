import Mathlib
import Definitions.Def_ScenarioReduction_BinaryTree_IStar

namespace ScenarioReduction.BinaryTree

theorem partner_exists (K : ℕ) (δ : ℕ → ℝ) (hδ : ∀ k ∈ Finset.Icc 1 K, 0 ≤ δ k)
    (hK : 3 ≤ K) (k0 : ℕ) (hk0 : k0 ∈ Finset.Icc 1 K)
    (hmin : ∀ k ∈ Finset.Icc 1 K, δ k0 ≤ δ k) (hk0K : k0 ≤ K - 2)
    (hmax : max (δ (k0 + 1)) (δ (k0 + 2)) ≤ 2 * δ k0) :
    ∀ j ∉ IStar K k0, ∃ i ∈ IStar K k0, ‖scenario δ i - scenario δ j‖ = 2 * δ k0 := by sorry

end ScenarioReduction.BinaryTree

