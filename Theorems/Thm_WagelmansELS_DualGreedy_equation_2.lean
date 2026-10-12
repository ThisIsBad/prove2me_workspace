import Mathlib
import Definitions.Def_WagelmansELS_DualGreedy_Greedy

namespace WagelmansELS.DualGreedy

theorem equation_2 (P : Instance) (v : ℕ → ℝ)
    (hd : ∀ t, 1 ≤ t → t ≤ P.n → 0 ≤ P.d t)
    (hf : ∀ i, 1 ≤ i → i ≤ P.n → 0 ≤ P.f i)
    (hv : IsGreedyForward P v)
    (j k : ℕ) (hj1 : 1 ≤ j) (hjn : j ≤ P.n) (hdj : 0 < P.d j)
    (hk1 : 1 ≤ k) (hkj : k ≤ j)
    (hk : v j = greedyBound P v k j)
    (hind : objective P v (k - 1) = F P (k - 1)) :
    objective P v j = P.f k + P.c k * demand P k j + F P (k - 1) := by sorry

end WagelmansELS.DualGreedy

