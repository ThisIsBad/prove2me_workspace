import Mathlib
import Definitions.Def_WagelmansELS_DualGreedy_Greedy

namespace WagelmansELS.DualGreedy

theorem greedy_forward_optimal (P : Instance) (v : ℕ → ℝ)
    (hd : ∀ t, 1 ≤ t → t ≤ P.n → 0 ≤ P.d t)
    (hf : ∀ i, 1 ≤ i → i ≤ P.n → 0 ≤ P.f i)
    (hv : IsGreedyForward P v) :
    IsFeasible P v ∧
      (∀ j, 1 ≤ j → j ≤ P.n → objective P v j = F P j) ∧
      (∀ u, IsFeasible P u → objective P u P.n ≤ objective P v P.n) := by sorry

end WagelmansELS.DualGreedy

