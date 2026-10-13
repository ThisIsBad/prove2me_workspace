import Mathlib
import Definitions.Def_TopkisRation_Levels_Model

namespace TopkisRation.Levels

theorem corollary_1 {n : ℕ} (M : Model n) (hM : M.Standing) (t : ℕ) (ht : t ∈ Finset.Icc 1 M.k)
    (z : ℝ) (hz : 0 ≤ z) (B : Fin n → ℝ) (hB : 0 ≤ B) :
    ∃ u ∈ feasible z B, M.f t z B = M.obj t (M.g (t - 1)) z B u ∧
      ∀ j i : Fin n, u j < B j → j < i → u i = 0 := by sorry

end TopkisRation.Levels

