import Mathlib
import Definitions.Def_LLLFactor_Reduction_Algorithm

namespace LLLFactor.Reduction

theorem step_preserves_situation {n : ℕ} (b b' : Fin n → LLLFactor.RedBasis.Vec n) (k k' : ℕ)
    (hb : LinearIndependent ℝ b) (hsit : Situation b k)
    (hstep : Step (b, k) (b', k')) :
    Situation b' k' ∧ 1 ≤ k' ∧ k' ≤ n + 1 := by sorry

end LLLFactor.Reduction

