import Mathlib
import Definitions.Def_WagelmansELS_DualGreedy_Greedy

namespace WagelmansELS.DualGreedy

theorem greedy_forward_monotone (P : Instance) (v : ℕ → ℝ)
    (hd : ∀ t, 1 ≤ t → t ≤ P.n → 0 ≤ P.d t)
    (hf : ∀ i, 1 ≤ i → i ≤ P.n → 0 ≤ P.f i)
    (hv : IsGreedyForward P v)
    (t j : ℕ) (ht : 1 ≤ t) (htj : t < j) (hjn : j ≤ P.n)
    (hdt : 0 < P.d t) (hdj : 0 < P.d j) : v j ≤ v t := by sorry

end WagelmansELS.DualGreedy

