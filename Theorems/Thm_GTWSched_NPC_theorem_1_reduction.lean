import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_GTWSched_NPC_Schedules
import Definitions.Def_GTWSched_NPC_Problems

namespace GTWSched.NPC

/-- Proof of THEOREM 1, pp. 336–337: for an even-odd partition instance `X` with `x₁ > 1`, the
instance D (lengths `l₀ = x₁ − 1`, `lᵢ = xᵢ`, `l₂ₙ₊₁ = 2`; midtimes `M = ∑ᵢ₌₀²ⁿ lᵢ/2` for
`T₀, …, T₂ₙ` and `2M + l₂ₙ₊₁/2` for `T₂ₙ₊₁`; threshold `k`) has a schedule of cost at most `k`
iff `X` has an even-odd partition into two parts of equal sum. -/
theorem theorem_1_reduction (x : List ℕ) (hx : EOInstance x) (hx1 : 1 < x.getD 0 0) :
    EOYes x ↔ TDYesReal (dLen x) (dMid x) (dK x) := by sorry

end GTWSched.NPC

