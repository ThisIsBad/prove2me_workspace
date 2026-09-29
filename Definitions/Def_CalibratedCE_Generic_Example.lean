import Mathlib

namespace CalibratedCE.Generic

/-- Row's payoffs in the 3 × 3 game of Foster–Vohra p. 48. Rows `A, B, C` are `0, 1, 2`,
columns `1, 2, 3` are `0, 1, 2`. -/
def exU₁ : Fin 3 → Fin 3 → ℝ := ![![2, 0, 0], ![2, 0, 0], ![2, 1, 1]]

/-- Column's payoffs in the 3 × 3 game of Foster–Vohra p. 48. -/
def exU₂ : Fin 3 → Fin 3 → ℝ := ![![2, 3, 1], ![2, 1, 3], ![0, 1, 0]]

/-- Row randomizes between `A` and `B` with equal probability and Column plays `1`. -/
noncomputable def exD₀ : Fin 3 → Fin 3 → ℝ :=
  fun a b => if b = 0 ∧ (a = 0 ∨ a = 1) then 1 / 2 else 0

/-- The point mass on `(C, 2)`. -/
def exDelta : Fin 3 → Fin 3 → ℝ :=
  fun a b => if a = 2 ∧ b = 1 then 1 else 0

end CalibratedCE.Generic
