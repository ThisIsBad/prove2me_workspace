import Mathlib
import Definitions.Def_SchedComplexity_Tardiness_Construction

namespace SchedComplexity.Tardiness

/-- Inequality (5) of the proof of Theorem 4(d), p. 21: for every processing order `π` there is an
order `π'` with the same jobs in the first `t` positions (hence `c_π' = c_π`) such that
`Σ_{j>t} (C_π'(j) − C_π'(t)) ≤ ½t'(t'+1)τ + ½(t+1)(A − b − c_π)`. -/
theorem ineq_5 {t : ℕ} (a : Fin t → ℕ) (b τ : ℕ)
    (ha : ∀ j, 0 < a j) (hb : 0 < b) (hbA : b < bigA a)
    (hτ : 2 * tPrime a b + bigA a < τ)
    (π : Equiv.Perm (Fin (t + tPrime a b))) :
    ∃ π' : Equiv.Perm (Fin (t + tPrime a b)),
      (∀ i : Fin (t + tPrime a b), i.val < t → π' i = π i) ∧
      (tailWeighted (wtP a b τ) (fun _ => 1) π' t : ℝ) ≤
        (1 / 2 : ℝ) * tPrime a b * (tPrime a b + 1) * τ
          + (1 / 2 : ℝ) * (t + 1) * ((bigA a : ℝ) - b - cPi a b τ π) := by sorry

end SchedComplexity.Tardiness

