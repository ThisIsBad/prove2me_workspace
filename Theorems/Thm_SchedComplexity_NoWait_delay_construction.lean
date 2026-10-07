import Mathlib
import Definitions.Def_SchedComplexity_NoWait_Construction

namespace SchedComplexity.NoWait

/-- p. 25: in the construction of Theorem 5, for an admissible `ι`, `λ ≥ 1`, `μ ≥ 2λ + 3` and
distinct jobs `j ≠ k`, the delay (9) is `c_{jk} = μ + 2λ` if `(j,k) ∈ A` and `μ + 2λ + 2` if
`(j,k) ∉ A`. -/
theorem delay_construction {n : ℕ} (adj : Fin n → Fin n → Bool) (ι : Fin n → Fin n → ℕ)
    (hι : Admissible n ι) (lam mu : ℕ) (hlam : 1 ≤ lam) (hmu : 2 * lam + 3 ≤ mu)
    (j k : Fin n) (hjk : j ≠ k) :
    delay (procTimes adj ι lam mu) (numMachines_pos n) j k =
      if adj j k = true then (mu : ℤ) + 2 * lam else (mu : ℤ) + 2 * lam + 2 := by sorry

end SchedComplexity.NoWait

