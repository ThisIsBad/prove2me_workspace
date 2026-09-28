import Mathlib
import Definitions.Def_ScenarioReduction_TernaryTree_scenario

namespace ScenarioReduction.TernaryTree

theorem dist_ge_delta_k0 (K : ℕ) (δ : ℕ → ℝ) (hδ : ∀ k ∈ Finset.Icc 1 K, 0 ≤ δ k)
    (k0 : ℕ) (hk0 : k0 ∈ Finset.Icc 1 K) (hmin : ∀ k ∈ Finset.Icc 1 K, δ k0 ≤ δ k)
    (σ τ : Fin K → Fin 3) (hστ : σ ≠ τ) :
    δ k0 ≤ ‖scenario δ σ - scenario δ τ‖ := by sorry

end ScenarioReduction.TernaryTree

