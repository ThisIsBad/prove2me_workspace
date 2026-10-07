import Mathlib
import Definitions.Def_SchedComplexity_Tardiness_Construction
import Definitions.Def_SchedComplexity_Tardiness_Knapsack

namespace SchedComplexity.Tardiness

/-- Proof of Theorem 4(d), p. 20: KNAPSACK has a solution iff some processing order `π` of the
constructed jobs has `C_π(t) = tτ + b`; and `−b ≤ c_π ≤ A − b` for every order `π`. -/
theorem knapsack_iff_split {t : ℕ} (a : Fin t → ℕ) (b τ : ℕ)
    (ha : ∀ j, 0 < a j) (hb : 0 < b) (hbA : b < bigA a)
    (hτ : 2 * tPrime a b + bigA a < τ) :
    (KnapsackYes a b ↔
      ∃ π : Equiv.Perm (Fin (t + tPrime a b)), posCompletion (wtP a b τ) π t = t * τ + b) ∧
    ∀ π : Equiv.Perm (Fin (t + tPrime a b)),
      -(b : ℤ) ≤ cPi a b τ π ∧ cPi a b τ π ≤ (bigA a : ℤ) - b := by sorry

end SchedComplexity.Tardiness

