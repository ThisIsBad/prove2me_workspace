import Mathlib
import Definitions.Def_JohnsonApprox_SubsetSum_Problem
import Definitions.Def_JohnsonApprox_SubsetSum_Ak

namespace JohnsonApprox.SubsetSum

theorem subsetSum_Ak_ratio (k : ℕ) (hk : 1 ≤ k) :
    (∀ (α : Type) [DecidableEq α] (u : Input α) (T₁ : Finset α), Choosable k u T₁ →
        (k : ℚ) * opt u ≤ ((k : ℚ) + 1) * measure u T₁) ∧
      (∀ δ : ℚ, 0 < δ → ∃ (u : Input ℕ) (T₁ : Finset ℕ), Choosable k u T₁ ∧
        0 < measure u T₁ ∧ (((k : ℚ) + 1) / k - δ) * measure u T₁ < opt u) := by sorry

end JohnsonApprox.SubsetSum

