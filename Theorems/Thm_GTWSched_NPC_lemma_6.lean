import Mathlib
import Definitions.Def_GTWSched_NPC_Schedules

namespace GTWSched.NPC

/-- LEMMA 6, p. 335: if `[Aₙ, …, A₁, T₀@M, B₁, …, Bₙ]` is a minimum cost schedule, then
`{Aᵢ, Bᵢ} = {T₂ᵢ, T₂ᵢ₋₁}` for every `i` (0-based `i`: the tasks `2i + 2` and `2i + 1`). -/
theorem lemma_6 {n : ℕ} (l : Fin (2 * n + 1) → ℝ) (M : ℝ) (hl0 : 0 < l 0)
    (hmono : StrictMono l) (hM : ∑ i, l i < M) (A B : Fin n → Fin (2 * n + 1))
    (hAB : IsBracket A B) (hmin : IsMinCost l M (centered l M A B)) (i : Fin n) :
    ({A i, B i} : Finset (Fin (2 * n + 1))) = {evenTask i, oddTask i} := by sorry

end GTWSched.NPC

