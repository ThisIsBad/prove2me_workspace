import Mathlib
import Definitions.Def_SchedComplexity_Tardiness_Construction

namespace SchedComplexity.Tardiness

/-- Claim (A) of the proof of Theorem 4(d), p. 20 (proof p. 21): if `c_π = 0`, then some processing
order `π'` has `c_π' = 0` and its schedule without idle time has `Σ w_j T_j ≤ y`. -/
theorem claim_A {t : ℕ} (a : Fin t → ℕ) (b τ : ℕ)
    (ha : ∀ j, 0 < a j) (hb : 0 < b) (hbA : b < bigA a)
    (hτ : 2 * tPrime a b + bigA a < τ)
    (π : Equiv.Perm (Fin (t + tPrime a b))) (hc : cPi a b τ π = 0) :
    ∃ π' : Equiv.Perm (Fin (t + tPrime a b)), cPi a b τ π' = 0 ∧
      orderTWT (wtP a b τ) (wtW a b τ) (wtD a b τ) π' ≤ (yThr a b τ : ℤ) := by sorry

end SchedComplexity.Tardiness

