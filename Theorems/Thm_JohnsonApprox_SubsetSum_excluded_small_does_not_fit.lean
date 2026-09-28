import Mathlib
import Definitions.Def_JohnsonApprox_SubsetSum_Problem
import Definitions.Def_JohnsonApprox_SubsetSum_Ak

namespace JohnsonApprox.SubsetSum

theorem excluded_small_does_not_fit {α : Type} [DecidableEq α] (k : ℕ) (hk : 1 ≤ k)
    (u : Input α) (T₁ : Finset α) (hT₁ : Choosable k u T₁) (x : α) (hxT : x ∈ u.T)
    (hxT₁ : x ∉ T₁) (hsmall : u.s x ≤ u.b / ((k : ℚ) + 1)) :
    u.b < u.s x + measure u T₁ ∧
      (k : ℚ) * u.b < ((k : ℚ) + 1) * measure u T₁ ∧
      (k : ℚ) * opt u ≤ ((k : ℚ) + 1) * measure u T₁ := by sorry

end JohnsonApprox.SubsetSum

