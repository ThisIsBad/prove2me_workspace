import Mathlib
import Definitions.Def_NQueensComp_NPC_Queens

namespace NQueensComp.NPC

/-- Observation 29, p. 834: for integers `a₁, a₂, c₁, c₂, d₁, d₂` with `0 ≤ a₁, a₂ ≤ 2` and
`0 ≤ d₁, d₂ ≤ 6`, if `21(c₁ − c₂) ± 7(a₁ − a₂) ± (d₁ − d₂) = 0` (either choice of each sign) then
`c₁ = c₂`, `a₁ = a₂` and `d₁ = d₂`. -/
theorem observation_29 (a₁ a₂ c₁ c₂ d₁ d₂ s₁ s₂ : ℤ)
    (ha₁ : 0 ≤ a₁ ∧ a₁ ≤ 2) (ha₂ : 0 ≤ a₂ ∧ a₂ ≤ 2) (hd₁ : 0 ≤ d₁ ∧ d₁ ≤ 6)
    (hd₂ : 0 ≤ d₂ ∧ d₂ ≤ 6) (hs₁ : s₁ = 1 ∨ s₁ = -1) (hs₂ : s₂ = 1 ∨ s₂ = -1)
    (h : 21 * (c₁ - c₂) + s₁ * (7 * (a₁ - a₂)) + s₂ * (d₁ - d₂) = 0) :
    c₁ = c₂ ∧ a₁ = a₂ ∧ d₁ = d₂ := by sorry

end NQueensComp.NPC

