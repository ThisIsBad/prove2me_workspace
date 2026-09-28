import Mathlib
import Definitions.Def_ScenarioReduction_TernaryTree_scenario
import Definitions.Def_ScenarioReduction_TernaryTree_IStarStar

namespace ScenarioReduction.TernaryTree

theorem partner_in_IStarStar (K : ℕ) (hK : 3 ≤ K) (δ : ℕ → ℝ)
    (hδ : ∀ k ∈ Finset.Icc 1 K, 0 ≤ δ k)
    (k0 : ℕ) (hk0 : k0 ∈ Finset.Icc 1 K) (hmin : ∀ k ∈ Finset.Icc 1 K, δ k0 ≤ δ k)
    (hk0K : k0 ≤ K - 2) (hmax : max (δ (k0 + 1)) (δ (k0 + 2)) ≤ 2 * δ k0) :
    ∀ j ∉ IStarStar K k0, ∃ i ∈ IStarStar K k0, ‖scenario δ i - scenario δ j‖ = δ k0 := by sorry

end ScenarioReduction.TernaryTree

