import Mathlib
import Definitions.Def_GTWSched_NPC_Schedules

namespace GTWSched.NPC

/-- p. 336: in the special case, the cost of every minimum cost schedule is
`∑ᵢ₌₁ⁿ (l₂ᵢ + l₂ᵢ₋₁)(n − i + 1/2) + (l₀)n`. -/
theorem min_cost_eq {n : ℕ} (l : Fin (2 * n + 1) → ℝ) (M : ℝ) (hl0 : 0 < l 0)
    (hmono : StrictMono l) (hM : ∑ i, l i < M) (s : Fin (2 * n + 1) → ℝ)
    (hs : IsMinCost l M s) : commonCost l M s = kStar l := by sorry

end GTWSched.NPC

