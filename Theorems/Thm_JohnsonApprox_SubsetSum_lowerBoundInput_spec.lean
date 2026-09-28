import Mathlib
import Definitions.Def_JohnsonApprox_SubsetSum_Problem
import Definitions.Def_JohnsonApprox_SubsetSum_Ak
import Definitions.Def_JohnsonApprox_SubsetSum_LowerBoundInput

namespace JohnsonApprox.SubsetSum

theorem lowerBoundInput_spec (k : ℕ) (hk : 1 ≤ k) (ε : ℚ) (hε : 0 < ε) (hε1 : ε < 1) :
    opt (lowerBoundInput k ε hε) = (k : ℚ) + 1 ∧
      (∀ T₁, Choosable k (lowerBoundInput k ε hε) T₁ →
        measure (lowerBoundInput k ε hε) T₁ = (k : ℚ) + ε) ∧
      ∃ T₁, Choosable k (lowerBoundInput k ε hε) T₁ := by sorry

end JohnsonApprox.SubsetSum

