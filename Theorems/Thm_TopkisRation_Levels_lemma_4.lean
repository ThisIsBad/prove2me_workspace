import Mathlib
import Definitions.Def_TopkisRation_Levels_Model
import Definitions.Def_TopkisRation_Levels_Split

namespace TopkisRation.Levels

theorem lemma_4 {n : ℕ} (M : Model n) (hM : M.Standing) (t : ℕ) (ht : t ∈ Finset.Icc 1 M.k)
    (z : ℝ) (hz : 0 ≤ z) (B : Fin n → ℝ) (hB : 0 ≤ B)
    (w : ℝ) (hw : w ∈ Set.Icc (max (z - ∑ j, B j) 0) z) :
    uVec (z - w) B ∈ {u : Fin n → ℝ | 0 ≤ u ∧ u ≤ B ∧ ∑ j, (B j - u j) = z - w} ∧
    ∀ u ∈ {u : Fin n → ℝ | 0 ≤ u ∧ u ≤ B ∧ ∑ j, (B j - u j) = z - w},
      M.p t ⬝ᵥ uVec (z - w) B + M.g (t - 1) w (M.a t • uVec (z - w) B) ≤
        M.p t ⬝ᵥ u + M.g (t - 1) w (M.a t • u) := by sorry

end TopkisRation.Levels

