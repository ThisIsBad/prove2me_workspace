import Mathlib
import Definitions.Def_WagelmansELS_DualGreedy_Greedy

namespace WagelmansELS.DualGreedy

theorem greedy_forward_feasible (P : Instance) (v : ℕ → ℝ)
    (hd : ∀ t, 1 ≤ t → t ≤ P.n → 0 ≤ P.d t)
    (hf : ∀ i, 1 ≤ i → i ≤ P.n → 0 ≤ P.f i)
    (hv : IsGreedyForward P v) : IsFeasible P v := by sorry

end WagelmansELS.DualGreedy

