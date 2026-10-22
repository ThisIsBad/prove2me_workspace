import Mathlib
import Definitions.Def_LLLFactor_Reduction_Algorithm

namespace LLLFactor.Reduction

theorem gram_lower_bound {n : ℕ} (hn : 0 < n) (c : Fin n → LLLFactor.RedBasis.Vec n)
    (L : Submodule ℤ (LLLFactor.RedBasis.Vec n)) (hc : LLLFactor.RedBasis.IsBasisFor c L) :
    0 < minSqNorm L ∧
    (∃ x ∈ L, x ≠ 0 ∧ ‖x‖ ^ 2 = minSqNorm L) ∧
    ∀ i : ℕ, 1 ≤ i → i ≤ n →
      (3 / 4 : ℝ) ^ (i * (i - 1) / 2) * minSqNorm L ^ i ≤ gram c i := by sorry

end LLLFactor.Reduction

