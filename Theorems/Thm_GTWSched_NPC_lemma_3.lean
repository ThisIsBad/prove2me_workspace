import Mathlib
import Definitions.Def_GTWSched_NPC_Schedules

namespace GTWSched.NPC

/-- LEMMA 3, p. 334: in the special case, a minimum cost schedule has `|A(S)| = |B(S)|`. -/
theorem lemma_3 {n : ℕ} (l : Fin (2 * n + 1) → ℝ) (M : ℝ) (hl0 : 0 < l 0)
    (hmono : StrictMono l) (hM : ∑ i, l i < M) (s : Fin (2 * n + 1) → ℝ)
    (hs : IsMinCost l M s) : (setA l M s).card = (setB l M s).card := by sorry

end GTWSched.NPC

