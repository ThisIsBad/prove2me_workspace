import Mathlib
import Definitions.Def_SchedComplexity_NoWait_Construction

namespace SchedComplexity.NoWait

/-- p. 25: "Through the choice of μ, these processing times are all strictly positive integers":
for an admissible `ι`, `λ ≥ 1` and `μ ≥ 2λ + 3`, every processing time `p_{ℓ i}` of the
construction is at least `1`. -/
theorem procTimes_pos {n : ℕ} (adj : Fin n → Fin n → Bool) (ι : Fin n → Fin n → ℕ)
    (hι : Admissible n ι) (lam mu : ℕ) (hlam : 1 ≤ lam) (hmu : 2 * lam + 3 ≤ mu)
    (ℓ : Fin n) (r : Fin (numMachines n)) :
    1 ≤ procTimeInt adj ι lam mu ℓ r := by sorry

end SchedComplexity.NoWait

