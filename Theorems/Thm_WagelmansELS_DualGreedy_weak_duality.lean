import Mathlib
import Definitions.Def_WagelmansELS_DualGreedy_Model

namespace WagelmansELS.DualGreedy

theorem weak_duality (P : Instance) (u : ℕ → ℝ)
    (hd : ∀ t, 1 ≤ t → t ≤ P.n → 0 ≤ P.d t)
    (hf : ∀ i, 1 ≤ i → i ≤ P.n → 0 ≤ P.f i)
    (hu : IsFeasible P u)
    (j : ℕ) (hj1 : 1 ≤ j) (hjn : j ≤ P.n) :
    objective P u j ≤ F P j := by sorry

end WagelmansELS.DualGreedy

