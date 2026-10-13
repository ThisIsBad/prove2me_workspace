import Mathlib
import Definitions.Def_SendSplit_Existence_Network
import Definitions.Def_SendSplit_Existence_AugmentedGraph

namespace SendSplit.Existence

theorem simpleCirculation_cost_nonneg_iff {n : ℕ} (G : ArcGraph n) (c : Fin n → Fin n → ℝ → ℝ)
    (hc : IsConcaveArcCost G c) (y : Fin n → Fin n → ℝ) (hy : IsSimpleCirculation G y) :
    (∀ θ : ℝ, 0 ≤ θ → 0 ≤ flowCost G c (fun i j => θ * y i j)) ↔
      0 ≤ ∑ p ∈ support G y, slopeAtInfty (c p.1 p.2) := by sorry

end SendSplit.Existence

