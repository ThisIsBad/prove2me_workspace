import Mathlib
import Definitions.Def_JohnsonApprox_SubsetSum_Problem
import Definitions.Def_JohnsonApprox_SubsetSum_Ak

namespace JohnsonApprox.SubsetSum

theorem choosable_opt_or_large {α : Type} [DecidableEq α] (k : ℕ) (hk : 1 ≤ k) (u : Input α)
    (T₁ : Finset α) (hT₁ : Choosable k u T₁) :
    measure u T₁ = opt u ∨ (k : ℚ) * u.b ≤ ((k : ℚ) + 1) * measure u T₁ := by sorry

end JohnsonApprox.SubsetSum

