import Mathlib
import Definitions.Def_SchedComplexity_Tardiness_Construction

namespace SchedComplexity.Tardiness

/-- Inequality (4) of the proof of Theorem 4(d), p. 21: for every processing order `π`,
`Σ_{j>t} (C_π(j) − C_π(t)) ≥ ½t'(t'+1)τ`. -/
theorem ineq_4 {t : ℕ} (a : Fin t → ℕ) (b τ : ℕ)
    (ha : ∀ j, 0 < a j) (hb : 0 < b) (hbA : b < bigA a)
    (hτ : 2 * tPrime a b + bigA a < τ)
    (π : Equiv.Perm (Fin (t + tPrime a b))) :
    (1 / 2 : ℝ) * tPrime a b * (tPrime a b + 1) * τ ≤
      (tailWeighted (wtP a b τ) (fun _ => 1) π t : ℝ) := by sorry

end SchedComplexity.Tardiness

