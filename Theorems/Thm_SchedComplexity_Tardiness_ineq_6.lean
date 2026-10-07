import Mathlib
import Definitions.Def_SchedComplexity_Tardiness_Construction

namespace SchedComplexity.Tardiness

/-- Inequality (6) of the proof of Theorem 4(d), p. 21: for every processing order `π`,
`Σ_{j>t} w_π(j)(C_π(j) − C_π(t)) ≥ y − (t'+1)τc_π − t'`. -/
theorem ineq_6 {t : ℕ} (a : Fin t → ℕ) (b τ : ℕ)
    (ha : ∀ j, 0 < a j) (hb : 0 < b) (hbA : b < bigA a)
    (hτ : 2 * tPrime a b + bigA a < τ)
    (π : Equiv.Perm (Fin (t + tPrime a b))) :
    (yThr a b τ : ℝ) - (tPrime a b + 1) * (τ : ℝ) * cPi a b τ π - tPrime a b ≤
      (tailWeighted (wtP a b τ) (wtW a b τ) π t : ℝ) := by sorry

end SchedComplexity.Tardiness

