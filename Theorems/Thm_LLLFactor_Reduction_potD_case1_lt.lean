import Mathlib
import Definitions.Def_LLLFactor_Reduction_Algorithm

namespace LLLFactor.Reduction

theorem potD_case1_lt {n : ℕ} (b b' : Fin n → LLLFactor.RedBasis.Vec n) (k k' : ℕ)
    (hb : LinearIndependent ℝ b) :
    (Case1 (b, k) (b', k') →
      gram b' (k - 1) < (3 / 4 : ℝ) * gram b (k - 1) ∧
      (∀ i : ℕ, i ≤ n → i ≠ k - 1 → gram b' i = gram b i) ∧
      potD b' < (3 / 4 : ℝ) * potD b) ∧
    (Case2 (b, k) (b', k') → ∀ i : ℕ, i ≤ n → gram b' i = gram b i) := by sorry

end LLLFactor.Reduction

