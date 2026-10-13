import Mathlib
import Definitions.Def_GTWSched_NPC_Schedules

namespace GTWSched.NPC

/-- LEMMA 5, p. 335: swapping `Aᵢ` and `Bᵢ` in `[Aₙ, …, A₁, T₀@M, B₁, …, Bₙ]` does not change the
cost. -/
theorem lemma_5 {n : ℕ} (l : Fin (2 * n + 1) → ℝ) (M : ℝ) (hl0 : 0 < l 0)
    (hmono : StrictMono l) (hM : ∑ i, l i < M)
    (A B : Fin n → Fin (2 * n + 1)) (hAB : IsBracket A B)
    (hmin : IsMinCost l M (centered l M A B)) (i : Fin n) :
    commonCost l M (centered l M (Function.update A i (B i)) (Function.update B i (A i))) =
      commonCost l M (centered l M A B) := by sorry

end GTWSched.NPC

