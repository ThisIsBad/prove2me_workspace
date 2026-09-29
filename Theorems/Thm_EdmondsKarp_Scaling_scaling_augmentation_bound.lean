import Mathlib
import Definitions.Def_EdmondsKarp_Scaling_Transport
import Definitions.Def_EdmondsKarp_Scaling_Augmentation
import Definitions.Def_EdmondsKarp_Scaling_Run

namespace EdmondsKarp.Scaling

/-- Theorem 9 (p. 260). The number of flow augmentations in applying the scaling method to a
transportation problem with integral (positive) supplies `a_1, …, a_m` and demands `b_1, …, b_n`,
`∑ a_i = ∑ b_j`, nonnegative costs, and any `l` with all `a_i, b_j < 2^l`, is at most
`max(m, n) (2 + [log_2 (∑ a_i / max(m, n))])`, where `[·]` is the floor. -/
theorem scaling_augmentation_bound {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (a : Fin m → ℕ)
    (b : Fin n → ℕ) (d : Fin m → Fin n → ℝ) (ha : ∀ i, 0 < a i) (hb : ∀ j, 0 < b j)
    (hsum : ∑ i, a i = ∑ j, b j) (hd : ∀ i j, 0 ≤ d i j) (l : ℕ)
    (hla : ∀ i, a i < 2 ^ l) (hlb : ∀ j, b j < 2 ^ l) (K : ℕ → ℕ) (F : ℕ → ℕ → Flow m n)
    (hR : IsScalingRun a b d l K F) :
    ((∑ p ∈ Finset.range l, K p : ℕ) : ℤ) ≤
      ((max m n : ℕ) : ℤ) *
        (2 + ⌊Real.logb 2 (((∑ i, a i : ℕ) : ℝ) / ((max m n : ℕ) : ℝ))⌋) := by sorry

end EdmondsKarp.Scaling
