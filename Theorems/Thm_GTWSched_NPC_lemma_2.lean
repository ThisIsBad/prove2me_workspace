import Mathlib
import Definitions.Def_GTWSched_NPC_Schedules

namespace GTWSched.NPC

/-- LEMMA 2, p. 334: in the special case, a minimum cost schedule has some task with its midtime
at `M`. -/
theorem lemma_2 {n : ℕ} (l : Fin (2 * n + 1) → ℝ) (M : ℝ) (hl0 : 0 < l 0)
    (hmono : StrictMono l) (hM : ∑ i, l i < M) (s : Fin (2 * n + 1) → ℝ)
    (hs : IsMinCost l M s) : ∃ i, mid l s i = M := by sorry

end GTWSched.NPC

