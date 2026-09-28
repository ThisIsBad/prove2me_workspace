import Mathlib
import Definitions.Def_JohnsonApprox_SubsetSum_Problem
import Definitions.Def_JohnsonApprox_SubsetSum_Ak

namespace JohnsonApprox.SubsetSum

theorem step1_big_dominates {α : Type} [DecidableEq α] (k : ℕ) (hk : 1 ≤ k) (u : Input α)
    (T₀ T₁ : Finset α) (hT₁ : Choosable k u T₁) (hT₀ : IsFeasible u T₀) :
    measure u (bigPart k u T₀) ≤ measure u (bigPart k u T₁) := by sorry

end JohnsonApprox.SubsetSum

