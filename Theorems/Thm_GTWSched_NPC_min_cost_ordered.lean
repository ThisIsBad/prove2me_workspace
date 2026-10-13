import Mathlib
import Definitions.Def_GTWSched_NPC_Schedules

namespace GTWSched.NPC

/-- p. 333: in the special case (tasks `T₀, …, T₂ₙ` with `0 < l₀ < l₁ < ⋯ < l₂ₙ` and one common
preferred midtime `M > ∑ᵢ lᵢ`), a minimum cost schedule is ordered. -/
theorem min_cost_ordered {n : ℕ} (l : Fin (2 * n + 1) → ℝ) (M : ℝ) (hl0 : 0 < l 0)
    (hmono : StrictMono l) (hM : ∑ i, l i < M) (s : Fin (2 * n + 1) → ℝ)
    (hs : IsMinCost l M s) : Ordered l M s := by sorry

end GTWSched.NPC

